import OAI.Probability.SATVariance.RootDisintegration

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_sigma.{u_1, u_2} {ι : Type u_1} [Fintype ι] {α : ι → Type u_2}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] (f : (i : ι) × α i → ℝ) :
    favg f = ∑ i, ((Fintype.card (α i) : ℝ) / Fintype.card ((i : ι) × α i)) *
      favg (fun a => f ⟨i,a⟩) := by
  unfold favg
  rw [Fintype.sum_sigma, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hc : (Fintype.card (α i) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (α i) ≠ 0)
  field_simp

lemma favg_pi_product.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α]
    (f : ι → α → ℝ) :
    favg (fun x : ι → α => ∏ i, f i (x i)) = ∏ i, favg (f i) := by
  classical
  unfold favg
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp

lemma favg_pi_eval.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (i : ι) (f : α → ℝ) : favg (fun x : ι → α => f (x i)) = favg f := by
  classical
  have he := favg_equiv (Equiv.funSplitAt i α).symm (fun x : ι → α => f (x i))
  rw [← he, favg_prod]
  simp only [Equiv.funSplitAt_symm_apply]
  simp only [dite_true]
  simp_rw [favg_const]

lemma favg_pi_restrict.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (p : ι → Prop) [DecidablePred p] (f : ({i // p i} → α) → ℝ) :
    favg (fun x : ι → α => f (fun i => x i)) = favg f := by
  classical
  let e := Equiv.piEquivPiSubtypeProd p (fun _ : ι => α)
  have he := favg_equiv e.symm (fun x : ι → α => f (fun i : {i // p i} => x i))
  rw [← he, favg_prod]
  have hh : (fun a : {i // p i} → α =>
      favg (fun b : {i // ¬p i} → α => f (fun i => e.symm (a,b) i))) =
      fun a => f a := by
    funext a
    have hi : ∀ b : {i // ¬p i} → α, (fun i : {i // p i} => e.symm (a,b) i) = a := by
      intro b
      funext i
      simp [e, Equiv.piEquivPiSubtypeProd, i.property]
    simp_rw [hi]
    exact favg_const _
  rw [hh]

def clauseCastEquiv {u s t : ℕ} (h : s = t) : Clause u s ≃ Clause u t :=
  Equiv.cast (congrArg (Clause u) h)

lemma clauseRead_cast {u s t : ℕ} (h : s = t) (c : Clause u s) (v : Fin u) :
    clauseRead (clauseCastEquiv h c) v = clauseRead c v := by
  subst t
  rfl

abbrev RefreshNoise (u k : ℕ) := Clause u k × (Fin k → Clause u (k-1))

def trueRoot {k : ℕ} (t : RootType k) (a : Assignment k) (h : RootSatisfies t a) : Fin k :=
  h.choose

lemma trueRoot_spec {k : ℕ} (t : RootType k) (a : Assignment k) (h : RootSatisfies t a) :
    t (trueRoot t a h) = some (a (trueRoot t a h)) := h.choose_spec

def refreshPart {u k : ℕ} (t : RootType k) (a : Assignment k)
    (c : Clause u (k-rootSize t)) (z : RefreshNoise u k) : Clause u (k-rootSize t) :=
  if h : rootSize t = 0 then clauseCastEquiv (by omega) z.1
  else if h' : rootSize t = 1 ∧ RootSatisfies t a then
    clauseCastEquiv (by omega) (z.2 (trueRoot t a h'.2))
  else c

lemma favg_refreshPart {u k : ℕ} (hku : k ≤ u) (t : RootType k) (a : Assignment k)
    (f : Clause u (k-rootSize t) → ℝ) :
    favg (fun c => favg (fun z : RefreshNoise u k => f (refreshPart t a c z))) = favg f := by
  let := clause_nonempty u k hku
  let := clause_nonempty u (k-1) (by omega)
  let := clause_nonempty u (k-rootSize t) (by omega)
  by_cases h : rootSize t = 0
  · simp only [refreshPart, dite_eq_left h]
    have he :
        favg (fun z : RefreshNoise u k => f (clauseCastEquiv (by omega) z.1)) = favg f := by
      rw [favg_prod]
      dsimp only
      simp_rw [favg_const]
      exact favg_equiv (clauseCastEquiv (by omega)) f
    simp_rw [he]
    exact favg_const _
  · simp only [refreshPart, dite_eq_right h]
    by_cases h' : rootSize t = 1 ∧ RootSatisfies t a
    · simp only [dite_eq_left h']
      rw [favg_const]
      rw [favg_prod]
      dsimp only
      have hp := favg_pi_eval (trueRoot t a h'.2)
        (fun c : Clause u (k-1) => f (clauseCastEquiv (show k-1 = k-rootSize t by omega) c))
      rw [favg_const]
      exact hp.trans (favg_equiv (clauseCastEquiv (u := u) (s := k-1) (t := k-rootSize t) (by omega)) f)
    · simp only [dite_eq_right h']
      simp_rw [favg_const]

lemma favg_refresh_stationary {n k u : ℕ} (hku : k ≤ u)
    (e : Fin k ⊕ Fin u ≃ Fin n) (a : Assignment k) (f : Clause n k → ℝ) :
    favg (fun p : (t : RootType k) × Clause u (k-rootSize t) =>
      favg (fun z : RefreshNoise u k => f (mergeClause e p.1 (refreshPart p.1 a p.2 z)))) =
      favg f := by
  let (t : RootType k) : Nonempty (Clause u (k-rootSize t)) := clause_nonempty _ _ (by omega)
  trans favg (fun p : (t : RootType k) × Clause u (k-rootSize t) => mergeClause e p.1 p.2 |> f)
  · rw [favg_sigma, favg_sigma]
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    exact favg_refreshPart hku t a (fun c => f (mergeClause e t c))
  · exact favg_equiv (splitClauseEquiv e) f

def refreshClause {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) (a : Assignment k)
    (c : Clause n k) (z : RefreshNoise u k) : Clause n k :=
  let p := (splitClauseEquiv e).symm c
  mergeClause e p.1 (refreshPart p.1 a p.2 z)

lemma favg_refreshClause {n k u : ℕ} (hku : k ≤ u)
    (e : Fin k ⊕ Fin u ≃ Fin n) (a : Assignment k) (f : Clause n k → ℝ) :
    favg (fun c => favg (fun z : RefreshNoise u k => f (refreshClause e a c z))) = favg f := by
  calc
    _ = favg (fun p : (t : RootType k) × Clause u (k-rootSize t) =>
        favg (fun z : RefreshNoise u k => f (refreshClause e a (splitClauseEquiv e p) z))) :=
      (favg_equiv (splitClauseEquiv e) _).symm
    _ = favg (fun p : (t : RootType k) × Clause u (k-rootSize t) =>
        favg (fun z : RefreshNoise u k => f (mergeClause e p.1 (refreshPart p.1 a p.2 z)))) := by
      congr 1
      funext p
      congr 1
      funext z
      exact congrArg f (congrArg
        (fun q : (t : RootType k) × Clause u (k-rootSize t) =>
          mergeClause e q.1 (refreshPart q.1 a q.2 z))
        ((splitClauseEquiv e).symm_apply_apply p))
    _ = favg f := favg_refresh_stationary hku e a f

lemma favg_pointwise_refresh.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β]
    (R : α → β → α)
    (hR : ∀ f : α → ℝ, favg (fun a => favg (fun b => f (R a b))) = favg f)
    (m : ℕ) (f : (Fin m → α) → ℝ) :
    favg (fun x : Fin m → α => favg (fun z : Fin m → β => f (fun i => R (x i) (z i)))) =
      favg f := by
  induction m with
  | zero =>
    simp only [favg, Fintype.sum_unique, Fintype.card_unique, Nat.cast_one, div_one]
    congr 1
    funext i
    exact i.elim0
  | succ m ih =>
    rw [favg_cons]
    simp_rw [favg_cons (α := β)]
    have he (x : Fin m → α) (a : α) (z : Fin m → β) (b : β) :
        (fun i : Fin (m+1) => R ((Fin.cons a x : Fin (m+1) → α) i) ((Fin.cons b z : Fin (m+1) → β) i)) =
        Fin.cons (R a b) (fun i => R (x i) (z i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hf (x : Fin m → α) (a : α) (z : Fin m → β) (b : β) :
        f (fun i => R ((Fin.cons a x : Fin (m+1) → α) i) ((Fin.cons b z : Fin (m+1) → β) i)) =
        f (Fin.cons (R a b) (fun i => R (x i) (z i))) := congrArg f (he x a z b)
    simp_rw [hf]
    conv_lhs => arg 1; intro x; rw [favg_comm]
    have hsingle (x : Fin m → α) (z : Fin m → β) :
        favg (fun a => favg (fun b => f (Fin.cons (R a b) (fun i => R (x i) (z i))))) =
        favg (fun c => f (Fin.cons c (fun i => R (x i) (z i)))) :=
      hR (fun c : α => f (Fin.cons c (fun i : Fin m => R (x i) (z i))))
    simp_rw [hsingle]
    conv_lhs => arg 1; intro x; rw [favg_comm]
    rw [favg_comm]
    have htail (c : α) :
        favg (fun x : Fin m → α => favg (fun z : Fin m → β =>
          f (Fin.cons c (fun i => R (x i) (z i))))) =
        favg (fun x : Fin m → α => f (Fin.cons c x)) :=
      ih (fun x : Fin m → α => f (Fin.cons c x))
    simp_rw [htail]
    rw [favg_cons, favg_comm]

def pathReward.{u_1, u_2} {X : Type u_1} {α : Type u_2} (step : ℕ → α → X → X) (f : X → ℝ) :
    (m : ℕ) → (Fin m → α) → X → ℝ
  | 0, _, _ => 0
  | m+1, z, x => f x + pathReward (fun i => step (i+1)) f m (Fin.tail z) (step 0 (z 0) x)

def uniformStep.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] (step : ℕ → α → X → X)
    (i : ℕ) (f : X → ℝ) (x : X) : ℝ := favg (fun a => f (step i a x))

lemma uniformStep_mono.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] (step : ℕ → α → X → X) (i : ℕ) :
    Monotone (uniformStep step i) := by
  intro f g h x
  exact favg_mono fun _ => h _

lemma uniformStep_add.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] (step : ℕ → α → X → X)
    (i : ℕ) (f g : X → ℝ) :
    uniformStep step i (fun x => f x+g x) = fun x => uniformStep step i f x+uniformStep step i g x := by
  funext x
  exact favg_add _ _

lemma uniformStep_mul.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] (step : ℕ → α → X → X)
    (i : ℕ) (c : ℝ) (f : X → ℝ) :
    uniformStep step i (fun x => c*f x) = fun x => c*uniformStep step i f x := by
  funext x
  exact favg_mul _ _

lemma uniformStep_const.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] [Nonempty α]
    (step : ℕ → α → X → X) (i : ℕ) (c : ℝ) :
    uniformStep step i (fun _ => c) = fun _ => c := by
  funext x
  exact favg_const _

lemma uniformStep_add_const.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] [Nonempty α]
    (step : ℕ → α → X → X) (i : ℕ) (f : X → ℝ) (c : ℝ) :
    uniformStep step i (fun x => f x+c) = fun x => uniformStep step i f x+c := by
  rw [uniformStep_add, uniformStep_const]

lemma pathReward_avg.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] [Nonempty α]
    (step : ℕ → α → X → X) (f : X → ℝ) (m : ℕ) (x : X) :
    favg (fun z : Fin m → α => pathReward step f m z x) =
      markovSum (uniformStep step) f m x := by
  induction m generalizing step x with
  | zero => simp [pathReward, markovSum, favg_const]
  | succ m ih =>
    rw [favg_cons, favg_comm]
    simp only [pathReward, Fin.cons_zero, Fin.tail_cons, favg_add, favg_const]
    simp_rw [ih]
    rfl

lemma markovSum_mul.{u_1} {X : Type u_1} (P : ℕ → (X → ℝ) → X → ℝ)
    (hP : ∀ i c f, P i (fun x => c*f x) = fun x => c*P i f x)
    (c : ℝ) (f : X → ℝ) (m : ℕ) :
    markovSum P (fun x => c*f x) m = fun x => c*markovSum P f m x := by
  induction m generalizing P with
  | zero => funext x; simp [markovSum]
  | succ m ih =>
    rw [markovSum, ih _ (fun i => hP (i+1)), hP]
    funext x
    simp only [markovSum]
    ring

lemma pathReward_sq_potential.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] [Nonempty α]
    (step : ℕ → α → X → X) (f τ : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hτ : ∀ x, 0 ≤ τ x) (z : ℕ → ℝ)
    (hz : ∀ i, 0 ≤ z i)
    (hdrift : ∀ i x, f x + uniformStep step i τ x ≤ τ x+z i)
    {Z : ℝ} (m : ℕ) (hZ : (∑ i ∈ Finset.range m, z i) ≤ Z) (x : X) :
    favg (fun w : Fin m → α => (pathReward step f m w x)^2) ≤
      2 * markovSum (uniformStep step) (fun y => f y*(τ y+Z)) m x := by
  induction m generalizing step z x with
  | zero => simp [pathReward, markovSum, favg_const]
  | succ m ih =>
    have hzt : (∑ i ∈ Finset.range m, z (i+1)) ≤ Z := by
      rw [Finset.sum_range_succ'] at hZ
      linarith [hz 0]
    have hfuture : uniformStep step 0
        (markovSum (uniformStep (fun i => step (i+1))) f m) x ≤
        τ x+Z-f x := by
      have hh := uniformStep_mono step 0 (fun y =>
        markovSum_potential (uniformStep (fun i => step (i+1)))
          (uniformStep_mono _) (uniformStep_add_const _) f τ hτ (fun i => z (i+1))
          (fun i => hdrift (i+1)) m y) x
      rw [uniformStep_add_const] at hh
      rw [Finset.sum_range_succ'] at hZ
      linarith [hdrift 0 x]
    have hi := favg_mono (fun a : α =>
      ih (fun i => step (i+1)) (fun i => z (i+1)) (fun i => hz (i+1))
        (fun i => hdrift (i+1)) hzt (step 0 a x))
    rw [favg_mul] at hi
    rw [favg_cons, favg_comm]
    have hs (a : α) : favg (fun w : Fin m → α =>
        (pathReward step f (m+1) (Fin.cons a w) x)^2) =
        (f x)^2 + 2*f x * markovSum (uniformStep (fun i => step (i+1))) f m (step 0 a x) +
          favg (fun w : Fin m → α =>
            (pathReward (fun i => step (i+1)) f m w (step 0 a x))^2) := by
      simp only [pathReward, Fin.cons_zero, Fin.tail_cons, add_sq]
      rw [favg_add, favg_add, favg_const]
      rw [favg_mul, pathReward_avg]
    simp_rw [hs]
    rw [favg_add, favg_add, favg_const, favg_mul]
    change _ ≤ 2*(f x*(τ x+Z)+_)
    change favg _ ≤ 2*uniformStep step 0
      (markovSum (uniformStep (fun i => step (i+1))) (fun y => f y*(τ y+Z)) m) x at hi
    change f x^2 + 2*f x * uniformStep step 0
      (markovSum (uniformStep (fun i => step (i+1))) f m) x + _ ≤
      2*(f x*(τ x+Z)+uniformStep step 0
        (markovSum (uniformStep (fun i => step (i+1))) (fun y => f y*(τ y+Z)) m) x)
    nlinarith [mul_le_mul_of_nonneg_left hfuture (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hf x)),
      sq_nonneg (f x)]

end RandomKSAT

end

end OAI
