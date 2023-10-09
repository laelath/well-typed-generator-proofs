From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From GL Require Import Maps.

Definition option_bind {A B : Type} (f : A -> option B) (o : option A) : option B :=
  match o with
  | None => None
  | Some a => f a
  end.

(****************
 Type of types
 ****************)
Inductive ty : Type :=
  | ty_bool : ty (* Base types *)
  | ty_arr : tele_ty -> ty -> ty (* Function types *)
with tele_ty :=
  | ty_tele_mvar : string -> tele_ty (* Extensible variable *)
  | ty_tele_cons : ty -> tele_ty -> tele_ty. (* List *)

Scheme ty_tele_ty_ind := Induction for ty Sort Prop
  with tele_ty_ty_ind := Induction for tele_ty Sort Prop.

Combined Scheme ty_tele_ty_mutind from ty_tele_ty_ind, tele_ty_ty_ind.

(* nth type in the tele_ty list *)
Fixpoint tele_ty_ref (n : nat) (tele : tele_ty) : option ty :=
  match tele with
  | ty_tele_mvar _ => None
  | ty_tele_cons t tele' =>
    match n with
    | O => Some t
    | S n' => tele_ty_ref n' tele'
    end
  end.

(* extensible var of a tele_ty *)
Fixpoint tele_ty_alpha (tele : tele_ty) : string :=
  match tele with
  | ty_tele_mvar alpha => alpha
  | ty_tele_cons _ tele' => tele_ty_alpha tele'
  end.

(* length of a tele_ty *)
Fixpoint tele_ty_length (tele : tele_ty) : nat :=
  match tele with
  | ty_tele_mvar _ => O
  | ty_tele_cons _ tele' => S (tele_ty_length tele')
  end.

(*******************
 Type of expressions 
 *******************)

Inductive exp : Type :=
  | exp_true : exp (* true *)
  | exp_false : exp (* false *)
  | exp_lam : string -> tele_ty -> exp -> exp (* lambda x ty body *)
  | exp_if : exp -> exp -> exp -> exp (* if cond then else *)
  | exp_app : exp -> tele_exp -> exp (* apply f args *)
  (* nat is for telescope projection *)
  | exp_var : string -> nat -> exp (* x *)
  | exp_hole: ty -> exp (* []_ty *)
with tele_exp :=
  | exp_tele_mvar : string -> tele_exp (* extensible var alpha *)
  | exp_tele_cons : exp -> tele_exp -> tele_exp. (* extensible exp list *)

Scheme exp_tele_exp_ind := Induction for exp Sort Prop
  with tele_exp_exp_ind := Induction for tele_exp Sort Prop.

(*******************
 Type of expression contexts
 *******************)

Inductive ctx : Type :=
  | ctx_hole : ctx (* context terminal *)
  | ctx_lam : string -> tele_ty -> ctx -> ctx (* lambda x ty cxt *)
  | ctx_if1 : ctx -> exp -> exp -> ctx (* if ctx then else *)
  | ctx_if2 : exp -> ctx -> exp -> ctx (* if cond ctx else *)
  | ctx_if3 : exp -> exp -> ctx -> ctx (* if cond then ctx *)
  | ctx_app1 : ctx -> tele_exp -> ctx (* apply cxt args *)
  | ctx_app2 : exp -> tele_ctx -> ctx (* apply f cxts *)
with tele_ctx :=
  | ctx_tele_cons1 : ctx -> tele_exp -> tele_ctx 
  | ctx_tele_cons2 : exp -> tele_ctx -> tele_ctx.

Scheme ctx_tele_ctx_ind := Induction for ctx Sort Prop
  with tele_ctx_ctx_ind := Induction for tele_ctx Sort Prop.

(* C[e] *)
Fixpoint plug (C : ctx) (e : exp) : exp :=
  match C with
  | ctx_hole => e
  | ctx_lam x t C' => exp_lam x t (plug C' e)
  | ctx_if1 C' e2 e3 => exp_if (plug C' e) e2 e3
  | ctx_if2 e1 C' e3 => exp_if e1 (plug C' e) e3
  | ctx_if3 e1 e2 C' => exp_if e1 e2 (plug C' e)
  | ctx_app1 C' te => exp_app (plug C' e) te
  | ctx_app2 e1 tc => exp_app e1 (plug_tele tc e)
  end
with plug_tele (TC : tele_ctx) (e : exp) : tele_exp :=
  match TC with
  | ctx_tele_cons1 C' te => exp_tele_cons (plug C' e) te
  | ctx_tele_cons2 e1 TC' => exp_tele_cons e1 (plug_tele TC' e)
  end.

Fixpoint plug_ctx (C1 : ctx) (C2 : ctx) : ctx :=
  match C1 with
  | ctx_hole => C2
  | ctx_lam x t C' => ctx_lam x t (plug_ctx C' C2)
  | ctx_if1 C' e2 e3 => ctx_if1 (plug_ctx C' C2) e2 e3
  | ctx_if2 e1 C' e3 => ctx_if2 e1 (plug_ctx C' C2) e3
  | ctx_if3 e1 e2 C' => ctx_if3 e1 e2 (plug_ctx C' C2)
  | ctx_app1 C' Te => ctx_app1 (plug_ctx C' C2) Te
  | ctx_app2 e1 TC => ctx_app2 e1 (plug_tele_ctx TC C2)
  end
with plug_tele_ctx (TC : tele_ctx) (C : ctx) : tele_ctx :=
  match TC with
  | ctx_tele_cons1 C' Te => ctx_tele_cons1 (plug_ctx C' C) Te
  | ctx_tele_cons2 e1 TC' => ctx_tele_cons2 e1 (plug_tele_ctx TC' C)
  end.

Theorem factor_plug : forall (C1 C2 : ctx) (e : exp),
  plug C1 (plug C2 e) = plug (plug_ctx C1 C2) e.
Proof.
  intros C1 C2 e.
  induction C1 using ctx_tele_ctx_ind with
    (P0 := fun (TC : tele_ctx) => plug_tele TC (plug C2 e) = plug_tele (plug_tele_ctx TC C2) e);
  try reflexivity;
  simpl; rewrite IHC1; reflexivity.
Qed.

Definition ty_context := partial_map tele_ty.
Definition ext_map := partial_map tele_ty.

(* TODO: use a more mathematically precise name for this *)
Definition combine_gammas (Gamma1 Gamma2 : ty_context) (x : string) :=
  match Gamma2 x with
  | None => Gamma1 x
  | Some TT => Some TT
  end.

(* Derives a context Gamma from the context C *)
Fixpoint context_gamma (C : ctx) :=
  match C with
  | ctx_hole => empty
  | ctx_lam x TT C' => combine_gammas (x |-> TT) (context_gamma C')
  | ctx_if1 C' e2 e3 => context_gamma C'
  | ctx_if2 e1 C' e3 => context_gamma C'
  | ctx_if3 e1 e2 C' => context_gamma C'
  | ctx_app1 C' es => context_gamma C'
  | ctx_app2 e CT => context_gamma_tele CT
  end
with context_gamma_tele (CT : tele_ctx) :=
  match CT with
  | ctx_tele_cons1 C es => context_gamma C
  | ctx_tele_cons2 e CT' => context_gamma_tele CT'
  end.

(* Does Gamma derive e : ty? *)
Inductive has_type : ty_context -> exp -> ty -> Prop :=
  | T_Hole : forall Gamma T, has_type Gamma (exp_hole T) T
  | T_True : forall Gamma, has_type Gamma exp_true ty_bool
  | T_False : forall Gamma, has_type Gamma exp_false ty_bool
  | T_If : forall Gamma e1 e2 e3 T,
      has_type Gamma e1 ty_bool ->
      has_type Gamma e2 T ->
      has_type Gamma e3 T ->
      has_type Gamma (exp_if e1 e2 e3) T
  | T_Var : forall Gamma x n T,
      option_bind (tele_ty_ref n) (Gamma x) = Some T ->
      has_type Gamma (exp_var x n) T
  | T_Lam : forall Gamma x TT e T,
      has_type (x |-> TT ; Gamma) e T ->
      has_type Gamma (exp_lam x TT e) (ty_arr TT T)
  | T_App : forall TT T2 Gamma e es,
      has_type Gamma e (ty_arr TT T2) ->
      has_type_tele Gamma es TT ->
      has_type Gamma (exp_app e es) T2
with has_type_tele : ty_context -> tele_exp -> tele_ty -> Prop :=
  | T_TeleMVar : forall Gamma alpha,
      has_type_tele Gamma (exp_tele_mvar alpha) (ty_tele_mvar alpha)
  | T_TeleCons : forall T TT Gamma e es,
      has_type Gamma e T ->
      has_type_tele Gamma es TT ->
      has_type_tele Gamma (exp_tele_cons e es) (ty_tele_cons T TT).

Scheme has_type_ty_tele_ind := Induction for has_type Sort Prop
  with has_type_tele_ty_ind := Induction for has_type_tele Sort Prop.

Fixpoint extend_mvar_ty (m : ext_map) (t : ty) :=
  match t with
  | ty_bool => ty_bool
  | ty_arr tele t' => ty_arr (extend_mvar_tele_ty m tele) (extend_mvar_ty m t')
  end
with extend_mvar_tele_ty (m : ext_map) (tele : tele_ty) :=
  match tele with
  | ty_tele_mvar alpha =>
    match m alpha with
    | None => ty_tele_mvar alpha
    | Some tele' => tele'
    end
  | ty_tele_cons t tele' => ty_tele_cons (extend_mvar_ty m t) (extend_mvar_tele_ty m tele')
  end.

Fixpoint tele_ty_to_tele_exp_holes (TTele : tele_ty) : tele_exp :=
  match TTele with
  | ty_tele_mvar alpha => exp_tele_mvar alpha
  | ty_tele_cons T TTele' => exp_tele_cons (exp_hole T) (tele_ty_to_tele_exp_holes TTele')
  end.

Lemma tele_ty_to_tele_exp_holes_well_typed : forall (Gamma : ty_context) (TT : tele_ty),
  has_type_tele Gamma (tele_ty_to_tele_exp_holes TT) TT.
Proof.
  intros Gamma TT.
  induction TT.
  - apply T_TeleMVar.
  - simpl. apply T_TeleCons.
    * apply T_Hole.
    * apply IHTT.
Qed.

(* Extend expression e with type extensions m. If m = {alpha -+> ty},
   e {alpha -+> ty} 
 *)
Fixpoint extend_mvar_exp (m : ext_map) (e : exp) :=
  match e with
  | exp_true => exp_true
  | exp_false => exp_false
  | exp_lam x TTele e' => exp_lam x (extend_mvar_tele_ty m TTele) (extend_mvar_exp m e')
  | exp_if e1 e2 e3 => exp_if (extend_mvar_exp m e1) (extend_mvar_exp m e2) (extend_mvar_exp m e3)
  | exp_app e1 es => exp_app (extend_mvar_exp m e1) (extend_mvar_tele_exp m es)
  | exp_var x n => exp_var x n
  | exp_hole T => exp_hole (extend_mvar_ty m T)
  end
with extend_mvar_tele_exp (m : ext_map) (es : tele_exp) :=
  match es with
  | exp_tele_mvar alpha =>
      match m alpha with
      | None => exp_tele_mvar alpha
      | Some TTele => tele_ty_to_tele_exp_holes TTele
      end
  | exp_tele_cons e es' => exp_tele_cons (extend_mvar_exp m e) (extend_mvar_tele_exp m es')
  end.

(* Extend context C with type extensions m. If m = {alpha -+> ty},
   C {alpha -+> ty} 
 *)
Fixpoint extend_mvar_ctx (m : ext_map) (C : ctx) :=
  match C with
  | ctx_hole => ctx_hole
  | ctx_lam x TTele C' => ctx_lam x (extend_mvar_tele_ty m TTele) (extend_mvar_ctx m C')
  | ctx_if1 C' e2 e3 => ctx_if1 (extend_mvar_ctx m C') (extend_mvar_exp m e2) (extend_mvar_exp m e3)
  | ctx_if2 e1 C' e3 => ctx_if2 (extend_mvar_exp m e1) (extend_mvar_ctx m C') (extend_mvar_exp m e3)
  | ctx_if3 e1 e2 C' => ctx_if3 (extend_mvar_exp m e1) (extend_mvar_exp m e2) (extend_mvar_ctx m C')
  | ctx_app1 C' es => ctx_app1 (extend_mvar_ctx m C') (extend_mvar_tele_exp m es)
  | ctx_app2 e CTele => ctx_app2 (extend_mvar_exp m e) (extend_mvar_tele_ctx m CTele)
  end
with extend_mvar_tele_ctx (m : ext_map) (CTele : tele_ctx) :=
  match CTele with
  | ctx_tele_cons1 C es => ctx_tele_cons1 (extend_mvar_ctx m C) (extend_mvar_tele_exp m es)
  | ctx_tele_cons2 e CTele' => ctx_tele_cons2 (extend_mvar_exp m e) (extend_mvar_tele_ctx m CTele')
  end.

Definition extend_mvar_gamma (m : ext_map) (Gamma : ty_context) :=
  fun x => option_map (extend_mvar_tele_ty m) (Gamma x).

(* append the extensions of two maps *)
Definition compose_mvar_maps (m1 m2 : ext_map) : ext_map :=
  fun x => match m2 x with
           | None => m1 x
           | Some tele => Some (extend_mvar_tele_ty m1 tele)
           end.

(* T ({alpha_1 -+> ty_1} compose {alpha_2 -+> ty_2}) 
   = 
   (T {alpha_2 -+> ty_2}) {alpha_1 -+> ty_1} 
*)
Theorem mvar_compose_correct_ty : forall (m1 m2 : ext_map),
  (forall (T : ty),
    extend_mvar_ty (compose_mvar_maps m1 m2) T =
    extend_mvar_ty m1 (extend_mvar_ty m2 T))
  /\
  (forall (TT : tele_ty),
    extend_mvar_tele_ty (compose_mvar_maps m1 m2) TT =
    extend_mvar_tele_ty m1 (extend_mvar_tele_ty m2 TT)).
Proof.
  intros m1 m2.
  apply ty_tele_ty_mutind.
  - (* ty_bool *)
    reflexivity.
  - (* ty_arr *)
    intros TT IHTT T IHT.
    simpl; f_equal; auto.
  - (* ty_tele_mvar *)
    intros alpha.
    simpl.
    unfold compose_mvar_maps.
    destruct (m2 alpha); auto.
  - (* ty_tele_cons *)
    intros T IHT TT IHTT.
    simpl; f_equal; auto.
Qed.

Theorem mvar_compose_correct_gamma : forall (m1 m2 : ext_map) (Gamma : ty_context),
  extend_mvar_gamma (compose_mvar_maps m1 m2) Gamma =
  extend_mvar_gamma m1 (extend_mvar_gamma m2 Gamma).
Proof.
  intros m1 m2 Gamma.
  apply functional_extensionality.
  intros x.
  unfold extend_mvar_gamma.
  destruct (Gamma x).
  - (* Some TT *)
    simpl.
    apply f_equal.
    apply mvar_compose_correct_ty.
  - (* None *)
    reflexivity.
Qed.

Lemma mvar_compose_correct_singleton : forall m x TT Gamma,
  (extend_mvar_gamma m (x |-> TT; Gamma)) =
  (x |-> extend_mvar_tele_ty m TT; extend_mvar_gamma m Gamma).
Proof.
  intros m x TT Gamma.
  apply functional_extensionality.
  intros x'.
  unfold extend_mvar_gamma.
  destruct (string_dec x x').
  - subst; repeat (rewrite update_eq); auto.
  - repeat (rewrite update_neq); auto.
Qed.

Fixpoint tele_ty_srec (P : ty -> Prop) (TT : tele_ty) :=
  match TT with
  | ty_tele_mvar x => True
  | ty_tele_cons T TT' => P T /\ tele_ty_srec P TT'
  end.

Lemma ty_ind' : forall (P : ty -> Prop),
                  P ty_bool ->
                  (forall t : tele_ty,
                   tele_ty_srec P t -> forall t0 : ty, P t0 -> P (ty_arr t t0)) ->
                  forall t : ty, P t.
Proof.
  intros P Hbool Harr T.
  apply (ty_tele_ty_ind P (tele_ty_srec P)).
  - apply Hbool.
  - apply Harr.
  - simpl.
    trivial.
  - simpl.
    split; trivial.
Qed.

Lemma extend_mvar_ty_empty : forall (T : ty),
  extend_mvar_ty empty T = T.
Proof.
  induction T using ty_tele_ty_ind with
    (P0 := fun (TT : tele_ty) => extend_mvar_tele_ty empty TT = TT); 
    auto; try (simpl; f_equal; auto).
Qed.

Fixpoint ty_has_alpha_bool (alpha : string) (T : ty) :=
  match T with
  | ty_bool => false
  | ty_arr TT T' => orb (ty_has_alpha_bool alpha T') (tele_ty_has_alpha_bool alpha TT)
  end
with tele_ty_has_alpha_bool (alpha : string) (TT : tele_ty) :=
  match TT with
  | ty_tele_mvar beta => eqb_string alpha beta
  | ty_tele_cons T TT' => orb (ty_has_alpha_bool alpha T) (tele_ty_has_alpha_bool alpha TT')
  end.

Fixpoint alpha_not_in_ty (alpha : string) (T : ty) :=
  match T with
  | ty_bool => True
  | ty_arr TT T' => (alpha_not_in_ty alpha T') /\ (alpha_not_in_tele_ty alpha TT)
  end
with alpha_not_in_tele_ty (alpha : string) (TT : tele_ty) :=
  match TT with
  | ty_tele_mvar beta => alpha <> beta
  | ty_tele_cons T TT' => (alpha_not_in_ty alpha T) /\ (alpha_not_in_tele_ty alpha TT')
  end.

Lemma extend_not_in : forall (alpha : string) (T : ty) (TT : tele_ty),
  alpha_not_in_ty alpha T ->
  extend_mvar_ty (alpha |-> TT) T = T.
Proof.
  intros alpha T TT; revert T.
  induction T using ty_tele_ty_ind with
    (P0 := fun (TT' : tele_ty) =>
             alpha_not_in_tele_ty alpha TT' ->
             extend_mvar_tele_ty (alpha |-> TT) TT' = TT');
    simpl; intros H.
  - (* ty_bool *)
    reflexivity.
  - (* ty_arr *)
    destruct H; apply f_equal2; auto.
  - (* ty_tele_mvar *)
    rewrite update_neq; [|apply H].
    reflexivity.
  - (* ty_tele_cons *)
    destruct H; apply f_equal2; auto.
Qed.

(* This is very much not structurally recursive *)
(*
Fixpoint unify_ty (T1 T2 : ty) : option ext_map :=
  match T1, T2 with
  | ty_bool, ty_bool => Some empty
  | ty_arr TT1 T1', ty_arr TT2 T2' =>
    match unify_tele_ty TT1 TT2 with
    | None => None
    | Some m =>
      match unify_ty (extend_mvar_ty m T1') (extend_mvar_ty m T2') with
      | None => None
      | Some m' => Some (compose_mvar_maps m' m)
      end
    end
  | _, _ => None
  end
with unify_tele_ty (TT1 TT2 : tele_ty) : option ext_map :=
  match TT1, TT2 with
  | ty_tele_mvar x, TT2 => Some (x |-> TT2)
  | TT1, ty_tele_mvar y => Some (y |-> TT1)
  | ty_tele_cons T1 TT1', ty_tele_cons T2 TT2' =>
    match unify_ty T1 T2 with
    | None => None
    | Some m =>
      match unify_tele_ty (extend_mvar_tele_ty m TT1') (extend_mvar_tele_ty m TT2') with
      | None => None
      | Some m' => Some (compose_mvar_maps m' m)
      end
    end
  end.
*)

Inductive gen_step : exp -> exp -> ext_map -> Prop :=
  (* C[[]_bool] ~~> C[true] *)
  | GST_true : forall C, gen_step (plug C (exp_hole ty_bool)) (plug C exp_true) empty
  (* C[[]_bool] ~~> C[false] *)
  | GST_false : forall C, gen_step (plug C (exp_hole ty_bool)) (plug C exp_false) empty
  (* C[[]_(alpha tys -> ty)] ~~> C[lambda x tys []_ty] *)
  | GST_lam : forall C x TTele T,
      gen_step (plug C (exp_hole (ty_arr TTele T)))
               (plug C (exp_lam x TTele (exp_hole T)))
               empty
  (* C[[]_ty] ~~> C[if []_bool []_ty []_ty] *)
  | GST_if : forall C T,
      gen_step (plug C (exp_hole T))
               (plug C (exp_if (exp_hole ty_bool) (exp_hole T) (exp_hole T)))
               empty
  (* C[[]_ty] ~~> C[x] if x : ty in Gamma(C) *)
  | GST_var : forall C x n T,
      option_bind (tele_ty_ref n) (context_gamma C x) = Some T ->
      gen_step (plug C (exp_hole T)) (plug C (exp_var x n)) empty
  (* C[[]_ty] ~~> m(C)[x] if x : ty' in Gamma(C) and m(ty) = m(ty') *)
  | GST_var_unify : forall C x n T T' m,
      option_bind (tele_ty_ref n) (context_gamma C x) = Some T' ->
      extend_mvar_ty m T' = extend_mvar_ty m T ->
      gen_step (plug C (exp_hole T)) (plug (extend_mvar_ctx m C) (exp_var x n)) m
  (* C_1[lambda x tys alpha C_2[[]_ty]] ~~>
     [alpha |-> ty](C_1)[lambda x (tys ty) alpha C_2[x]] if x not in C_2 *)
  | GST_var_ext : forall C1 C2 x TT T,
      let alpha := tele_ty_alpha TT in
      let m := alpha |-> ty_tele_cons T (ty_tele_mvar alpha) in
      let n := tele_ty_length TT in
      context_gamma C2 x = None ->
      alpha_not_in_ty alpha T ->
      gen_step (plug C1 (exp_lam x TT (plug C2 (exp_hole T))))
               (plug (extend_mvar_ctx m C1)
                     (exp_lam x (extend_mvar_tele_ty m TT)
                              (plug (extend_mvar_ctx m C2) (exp_var x n))))
               m
  (* C[[]_ty] ~~> C[[]_(alpha -> ty) alpha] *)
  | GST_app : forall C alpha T,
      gen_step (plug C (exp_hole T))
               (plug C (exp_app (exp_hole (ty_arr (ty_tele_mvar alpha) T)) (exp_tele_mvar alpha)))
               empty.

Lemma combine_gammas_assoc_singleton :
  forall Gamma Gamma' s t,
    (combine_gammas Gamma (combine_gammas (s |-> t) Gamma')) =
    (combine_gammas (s |-> t; Gamma) Gamma').
Proof.
  intros Gamma Gamma' s t.
  apply functional_extensionality.
  intros x.
  unfold combine_gammas.
  destruct (Gamma' x); auto.
  destruct (string_dec s x).
  - subst; repeat (rewrite update_eq); auto.
  - repeat (rewrite update_neq); auto.
Qed.

(* Gamma derives C[[]_T] : T' ->
   (Gamma . Gamma(C)) derives e : T ->
   Gamma derives C[e] : T'
*)
Lemma hole_replacement_consistent : forall (Gamma : ty_context) (C : ctx) (e : exp) (T T' : ty),
  has_type Gamma (plug C (exp_hole T)) T' ->
  has_type (combine_gammas Gamma (context_gamma C)) e T ->
  has_type Gamma (plug C e) T'.
Proof.
  intros Gamma C e T.
  generalize dependent Gamma.
  induction C using ctx_tele_ctx_ind with
    (P0 := fun (TC : tele_ctx) =>
             forall (Gamma : ty_context) (TT' : tele_ty),
               has_type_tele Gamma (plug_tele TC (exp_hole T)) TT' ->
               has_type (combine_gammas Gamma (context_gamma_tele TC)) e T ->
               has_type_tele Gamma (plug_tele TC e) TT');
    simpl; intros Gamma T' HC He;
    inversion HC; subst;
    (* ctx_hole *)
    auto;
    (* ctx_if *)
    try (apply T_If; auto);
    (* ctx_app *)
    try (eapply T_App; eauto);
    (* ctx_tele_cons *)
    try (apply T_TeleCons; auto).
    (* ctx_lam *)
    apply T_Lam.
    apply IHC; auto.
    rewrite <- combine_gammas_assoc_singleton; auto.
Qed.

(* C[e] {alpha -+> ty} = C {alpha -+> ty} [e {alpha -+> ty}] *)
Lemma extend_plug_distr : forall (m : ext_map) (C : ctx) (e : exp),
  extend_mvar_exp m (plug C e) = plug (extend_mvar_ctx m C) (extend_mvar_exp m e).
Proof.
  intros m C e.
  induction C using ctx_tele_ctx_ind with
    (P0 := (fun (TC : tele_ctx) =>
              (extend_mvar_tele_exp m (plug_tele TC e)) =
              (plug_tele (extend_mvar_tele_ctx m TC) (extend_mvar_exp m e))));
  auto;
  simpl; rewrite IHC; auto.
Qed.

Lemma extend_plug_ctx_distr : forall (m : ext_map) (C1 C2 : ctx),
  extend_mvar_ctx m (plug_ctx C1 C2) = plug_ctx (extend_mvar_ctx m C1) (extend_mvar_ctx m C2).
Proof.
  intros m C1 C2.
  induction C1 using ctx_tele_ctx_ind with
    (P0 := fun (TC : tele_ctx) =>
             extend_mvar_tele_ctx m (plug_tele_ctx TC C2) =
             plug_tele_ctx (extend_mvar_tele_ctx m TC) (extend_mvar_ctx m C2));
  auto;
  simpl; try rewrite IHC1; try rewrite IHC2; auto.
Qed.

(*
  C[lambda x tys e]{alpha -+> ty}
  =
  C{alpha -+> ty} [lambda x tys{alpha -+> ty} e{alpha -+> ty}]
*)
Lemma extract_plug_extend_lam : forall (m : ext_map) (C : ctx)
                                       (x : string) (TT : tele_ty) (e : exp),
  (plug (extend_mvar_ctx m C)
        (exp_lam x (extend_mvar_tele_ty m TT)
                   (extend_mvar_exp m e)))
  =
  (extend_mvar_exp m (plug C (exp_lam x TT e))).
Proof.
  intros m C x TT e.
  rewrite extend_plug_distr.
  f_equal.
Qed.

Lemma extend_tele_ty_ref : forall (TT : tele_ty) (T : ty) (n : nat) (m : ext_map),
  tele_ty_ref n TT = Some T ->
  tele_ty_ref n (extend_mvar_tele_ty m TT) = Some (extend_mvar_ty m T).
Proof.
  intros TT T n m; revert n.
  induction TT; intros n H.
  - (* ty_tele_mvar *)
    destruct n; discriminate.
  - (* ty_tele_cons *)
    destruct n; simpl in *.
    + inversion H; subst; auto.
    + auto.
Qed.

(* Gamma derives e : T ->
   Gamma{alpha -+> ty} derives e{alpha -+> ty} : T{alpha -+> ty}
*)
Lemma extend_mvar_consistent : forall (Gamma : ty_context) (m : ext_map)
                                      (e : exp) (T : ty),
  has_type Gamma e T ->
  has_type (extend_mvar_gamma m Gamma) (extend_mvar_exp m e) (extend_mvar_ty m T).
Proof.
  intros Gamma m e T H.
  induction H using has_type_ty_tele_ind with
    (P0 := (fun (Gamma : ty_context) (Te : tele_exp) (TT : tele_ty)
                (HT : has_type_tele Gamma Te TT) =>
              has_type_tele (extend_mvar_gamma m Gamma)
                            (extend_mvar_tele_exp m Te)
                            (extend_mvar_tele_ty m TT)));
    simpl; try (constructor; auto; fail).
  - apply T_Var.
    unfold extend_mvar_gamma.
    destruct (Gamma x); simpl in *.
    * apply extend_tele_ty_ref; auto.
    * discriminate.
  - apply T_Lam.
    rewrite <- mvar_compose_correct_singleton; auto.
  - eapply T_App; eauto.
  - destruct (m alpha).
    * apply tele_ty_to_tele_exp_holes_well_typed.
    * apply T_TeleMVar.
Qed.

Lemma extend_empty_noop_gamma : forall (Gamma : ty_context),
  extend_mvar_gamma empty Gamma = Gamma.
Proof.
  intros Gamma.
  apply functional_extensionality.
  intros x.
  unfold extend_mvar_gamma.
  destruct (Gamma x); auto.
  simpl; f_equal.
  (* TODO: already proven for tys, change lemma to be proving both *)
  induction t using tele_ty_ty_ind with
    (P := fun (T : ty) => extend_mvar_ty empty T = T);
  simpl; auto; f_equal; auto.
Qed.

Lemma combine_gammas_empty_noop : forall (Gamma : ty_context),
  combine_gammas empty Gamma = Gamma.
Proof.
  intros Gamma.
  apply functional_extensionality.
  intros x.
  unfold combine_gammas.
  destruct (Gamma x); auto.
Qed.

Lemma extend_context_gamma_preserves_names : forall (C : ctx) (m : ext_map) (x : string),
  context_gamma (extend_mvar_ctx m C) x = option_map (extend_mvar_tele_ty m) (context_gamma C x).
Proof.
  intros C m x; revert C m.
  induction C using ctx_tele_ctx_ind with
    (P0 := fun (TC : tele_ctx) => forall m : ext_map,
             context_gamma_tele (extend_mvar_tele_ctx m TC) x =
             option_map (extend_mvar_tele_ty m) (context_gamma_tele TC x));
    simpl; auto.
  - intros m.
    unfold combine_gammas.
    rewrite IHC.
    destruct (context_gamma C x); simpl; auto.
    destruct (string_dec s x).
    * subst; repeat (rewrite update_eq); auto.
    * repeat (rewrite update_neq); auto.
Qed.

Lemma extend_context_gamma_not_in : forall (C : ctx) (m : ext_map) (x : string),
  context_gamma C x = None -> context_gamma (extend_mvar_ctx m C) x = None.
Proof.
  intros C m x H.
  rewrite extend_context_gamma_preserves_names.
  rewrite H; auto.
Qed.

Lemma dist_context_gamma_plug : forall (C1 C2 : ctx),
  context_gamma (plug_ctx C1 C2) = combine_gammas (context_gamma C1) (context_gamma C2).
Proof.
  intros C1 C2.
  apply functional_extensionality.
  intros x.
  einduction C1 using ctx_tele_ctx_ind;
    simpl; auto.
  - rewrite combine_gammas_empty_noop; auto.
  - unfold combine_gammas in *.
    rewrite IHc.
    destruct (context_gamma C2 x); auto.
  - apply IHc.
  - apply IHc.
  - apply IHc.
Qed.

Lemma extend_ref_same : forall (TT : tele_ty) (n : nat) (T : ty) (alpha : string),
  alpha = tele_ty_alpha TT ->
  n = tele_ty_length TT ->
  tele_ty_ref n (extend_mvar_tele_ty (alpha |-> ty_tele_cons T (ty_tele_mvar alpha)) TT)
  = Some T.
Proof.
  intros TT n T alpha; revert TT.
  induction n; simpl; intros TT Ha Hn; destruct TT; simpl in *;
  try (discriminate).
  - subst; rewrite update_eq; auto.
  - apply IHn; auto.
Qed.

(* Gamma derives e1 : T ->
   e1 ~~>{alpha -+> ty} e2 ->
   Gamma{alpha -+> ty} derives e2 : T{alpha -+> ty}
*)
Theorem step_preserves_type : forall (e1 e2 : exp) (m : ext_map)
                                     (Gamma : ty_context) (T : ty),
  has_type Gamma e1 T ->
  gen_step e1 e2 m ->
  has_type (extend_mvar_gamma m Gamma) e2 (extend_mvar_ty m T).
Proof.
  intros e1 e2 m Gamma T Htype Hgen.
  generalize dependent T.
  destruct Hgen; intros T_ HT_.
  - (* GST_true *)
    rewrite extend_mvar_ty_empty.
    eapply hole_replacement_consistent.
    * rewrite extend_empty_noop_gamma.
      apply HT_.
    * apply T_True.
  - (* GST_false *)
    rewrite extend_mvar_ty_empty.
    eapply hole_replacement_consistent.
    * rewrite extend_empty_noop_gamma.
      apply HT_.
    * apply T_False.
  - (* GST_lam *)
    rewrite extend_mvar_ty_empty.
    eapply hole_replacement_consistent.
    * rewrite extend_empty_noop_gamma.
      apply HT_.
    * apply T_Lam.
      apply T_Hole.
  - (* GST_if *)
    rewrite extend_mvar_ty_empty.
    eapply hole_replacement_consistent.
    * rewrite extend_empty_noop_gamma.
      apply HT_.
    * apply T_If; apply T_Hole.
  - (* GST_var *)
    rewrite extend_mvar_ty_empty.
    eapply hole_replacement_consistent.
    * rewrite extend_empty_noop_gamma.
      apply HT_.
    * apply T_Var.
      unfold option_bind, combine_gammas.
      destruct (context_gamma C x); auto.
      discriminate.
  - (* GST_var_unify *)
    apply hole_replacement_consistent with (T := extend_mvar_ty m T).
      fold (extend_mvar_exp m (exp_hole T)).
      rewrite <- extend_plug_distr.
      apply extend_mvar_consistent.
      apply HT_.
    * rewrite <- H0.
      apply T_Var.
      unfold combine_gammas.
      rewrite extend_context_gamma_preserves_names.
      destruct (context_gamma C x).
      + simpl in *.
        apply extend_tele_ty_ref.
        apply H.
      + discriminate H.
  - (* GST_var_ext *)
    fold (extend_mvar_exp m (exp_var x n)).
    rewrite <- extend_plug_distr.
    unfold extend_mvar_exp; fold (extend_mvar_exp m (exp_lam x TT (plug C2 (exp_var x n)))).
    rewrite <- extend_plug_distr.
    unfold plug; fold (plug (ctx_lam x TT C2) (exp_var x n)); fold plug.
    rewrite factor_plug.
    rewrite extend_plug_distr.
    apply hole_replacement_consistent with (T := T).
    + apply extend_not_in with (TT := ty_tele_cons T (ty_tele_mvar alpha)) in H0.
      rewrite <- H0.
      apply extend_mvar_consistent with (m := m) in HT_.
      unfold plug in HT_; fold (plug (ctx_lam x TT C2) (exp_hole T)) in HT_; fold plug in HT_.
      rewrite factor_plug in HT_.
      rewrite extend_plug_distr in HT_.
      apply HT_.
    + apply T_Var.
      rewrite extend_plug_ctx_distr.
      rewrite dist_context_gamma_plug.
      destruct (context_gamma C2 x) eqn:G.
      * discriminate H.
      * simpl. unfold combine_gammas.
        rewrite extend_context_gamma_preserves_names.
        rewrite G.
        rewrite update_eq.
        apply extend_ref_same; reflexivity.
  - (* GST_app *)
    rewrite extend_mvar_ty_empty.
    eapply hole_replacement_consistent.
    * rewrite extend_empty_noop_gamma.
      apply HT_.
    * eapply T_App; constructor.
Qed.

(* TODO: this needs to be rewritten somehow *)
Inductive gen_multistep : exp -> exp -> ext_map -> Prop :=
  | GMST_refl : forall e, gen_multistep e e empty
  | GMST_trans : forall e1 e2 e3 m1 m2,
      gen_multistep e1 e2 m1 ->
      gen_multistep e2 e3 m2 ->
      gen_multistep e1 e3 (compose_mvar_maps m2 m1)
  | GMST_close : forall e1 e2 m,
      gen_step e1 e2 m ->
      gen_multistep e1 e2 m.

(* Gamma derives e1 : T ->
   e1 ~~>*{alpha -+> ty} e2 ->
   Gamma{alpha -+> ty} derives e2 : T{alpha -+> ty}
 *)
Theorem multistep_preserves_type : forall (e1 e2 : exp) (m : ext_map)
                                          (Gamma : ty_context) (T : ty),
  has_type Gamma e1 T ->
  gen_multistep e1 e2 m ->
  has_type (extend_mvar_gamma m Gamma) e2 (extend_mvar_ty m T).
Proof.
  intros e1 e2 m Gamma T Htype Hgen.
  generalize dependent T.
  generalize dependent Gamma.
  induction Hgen; intros Gamma T Htype.
  - rewrite extend_mvar_ty_empty, extend_empty_noop_gamma; auto.
  - rewrite (proj1 (mvar_compose_correct_ty m2 m1) T).
    rewrite mvar_compose_correct_gamma.
    auto.
  - eapply step_preserves_type; eauto.
Qed.








