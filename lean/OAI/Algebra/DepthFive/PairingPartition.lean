import OAI.Algebra.DepthFive.RelaxedPaths

namespace OAI

namespace Problem335.Pairings

open scoped BigOperators

instance {α : Type*} [DecidableEq α] (τ : Kind) (x : Labels α) :
    Decidable (ExactRespects τ x) := by
  cases τ <;> unfold ExactRespects <;> infer_instance

/-- Assign the all-equal case to normal pairing, as required for disjoint classes. -/
def classify {α : Type*} [DecidableEq α] (x : Labels α) : Kind :=
  if x.p = x.q then .normal else .diagonal

theorem exactRespects_classify_iff {α : Type*} [DecidableEq α] (x : Labels α) :
    ExactRespects (classify x) x ↔
      Finsupp.single x.p (1 : ℤ) - Finsupp.single x.q 1 =
        Finsupp.single x.r 1 - Finsupp.single x.s 1 := by
  rw [coordinate_difference_eq_iff_exclusive]
  by_cases h : x.p = x.q <;> simp [classify, ExactRespects, h]

theorem classify_eq_of_exact {α : Type*} [DecidableEq α] {τ : Kind} {x : Labels α}
    (h : ExactRespects τ x) : classify x = τ := by
  cases τ
  · simp [classify, h.1]
  · simp [classify, h.2.2]

/-- The four layer coordinates of endpoint-fixed paths. -/
def layerLabels {α : Type*} {L : ℕ} (a : α) (x : Fin L → Labels α)
    (t : Fin (L + 1)) : Labels (α × α) :=
  zipLabels (closePaths a x t.castSucc) (closePaths a x t.succ)

abbrev ExactPaths (α : Type*) {L : ℕ} (a : α) (τ : Fin (L + 1) → Kind) :=
  {x : Fin L → Labels α // ∀ t, ExactRespects (τ t) (layerLabels a x t)}

abbrev CompatiblePaths (α : Type*) {L : ℕ} (a : α) :=
  {x : Fin L → Labels α // ∀ t : Fin (L + 1),
    Finsupp.single (layerLabels a x t).p (1 : ℤ) -
      Finsupp.single (layerLabels a x t).q 1 =
    Finsupp.single (layerLabels a x t).r 1 -
      Finsupp.single (layerLabels a x t).s 1}

/-- The compatible quadruples partition uniquely according to their exact pairing word. -/
def compatiblePathsEquivSigma (α : Type*) [DecidableEq α] {L : ℕ} (a : α) :
    CompatiblePaths α (L := L) a ≃
      Σ τ : Fin (L + 1) → Kind, ExactPaths α a τ where
  toFun x := ⟨fun t => classify (layerLabels a x.1 t),
    ⟨x.1, fun t => (exactRespects_classify_iff _).mpr (x.2 t)⟩⟩
  invFun x := ⟨x.2.1, fun t =>
    (coordinate_difference_eq_iff_existsUnique _).mpr
      ⟨x.1 t, x.2.2 t, fun _ hk => exactRespects_unique hk (x.2.2 t)⟩⟩
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨τ, x⟩
    have hτ : (fun t => classify (layerLabels a x.1 t)) = τ :=
      funext (fun t => classify_eq_of_exact (x.2 t))
    apply Sigma.ext hτ
    have hp : ∀ y : Fin L → Labels α,
        (∀ t, ExactRespects (classify (layerLabels a x.1 t)) (layerLabels a y t)) ↔
          ∀ t, ExactRespects (τ t) (layerLabels a y t) := by
      intro y
      simp only [fun t => classify_eq_of_exact (x.2 t)]
    exact (Subtype.heq_iff_coe_eq hp).mpr rfl

/-- Regroup any finite weighted compatible-path sum by its unique pairing word. -/
theorem sum_compatiblePaths_eq_sum_exactPaths {α R : Type*}
    [Fintype α] [DecidableEq α] [AddCommMonoid R] {L : ℕ}
    (a : α) (w : (Fin L → Labels α) → R) :
    (∑ x : CompatiblePaths α (L := L) a, w x.1) =
      ∑ τ : Fin (L + 1) → Kind, ∑ x : ExactPaths α a τ, w x.1 := by
  classical
  simpa only [Fintype.sum_sigma] using
    (Fintype.sum_equiv (compatiblePathsEquivSigma α a)
      (fun x : CompatiblePaths α (L := L) a => w x.1)
      (fun x : Σ τ : Fin (L + 1) → Kind, ExactPaths α a τ => w x.2.1)
      (fun _ => rfl))

/-- Regroup sums whose weight remembers the canonical pairing word. -/
theorem sum_compatiblePaths_pairingWeight {α R : Type*}
    [Fintype α] [DecidableEq α] [AddCommMonoid R] {L : ℕ}
    (a : α) (w : (Fin (L + 1) → Kind) → (Fin L → Labels α) → R) :
    (∑ x : CompatiblePaths α (L := L) a,
      w (fun t => classify (layerLabels a x.1 t)) x.1) =
      ∑ τ : Fin (L + 1) → Kind, ∑ x : ExactPaths α a τ, w τ x.1 := by
  classical
  simpa only [Fintype.sum_sigma] using
    (Fintype.sum_equiv (compatiblePathsEquivSigma α a)
      (fun x : CompatiblePaths α (L := L) a =>
        w (fun t => classify (layerLabels a x.1 t)) x.1)
      (fun x : Σ τ : Fin (L + 1) → Kind, ExactPaths α a τ => w x.1 x.2.1)
      (fun _ => rfl))

/-- Enlarging a finite summation domain preserves inequalities for nonnegative weights. -/
theorem sum_subtype_le_of_imp {ι : Type*} [Fintype ι]
    (P Q : ι → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ x, P x → Q x) (w : ι → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x : {x // P x}, w x.1) ≤ ∑ x : {x // Q x}, w x.1 := by
  classical
  calc
    _ = ∑ x ∈ Finset.univ.filter P, w x :=
      (Finset.sum_subtype _ (by intro x; simp) w).symm
    _ ≤ ∑ x ∈ Finset.univ.filter Q, w x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hPQ x hx
      · intro x _ _
        exact hw x
    _ = _ := Finset.sum_subtype _ (by intro x; simp) w

/-- Dropping the diagonal inequalities introduces only nonnegative summands. -/
theorem sum_exactPaths_le_sum_relaxedPaths {α : Type*}
    [Fintype α] [DecidableEq α] {L : ℕ} (a : α)
    (τ : Fin (L + 1) → Kind) (w : (Fin L → Labels α) → ℝ)
    (hw : ∀ x, 0 ≤ w x) :
    (∑ x : ExactPaths α a τ, w x.1) ≤ ∑ x : RelaxedPaths α a τ, w x.1 := by
  apply sum_subtype_le_of_imp _ _ ?_ w hw
  intro x hx t
  exact (hx t).respects

/-- Exact grouping followed by relaxation: the combinatorial second-trace upper bound. -/
theorem sum_compatiblePaths_le_sum_relaxedPaths {α : Type*}
    [Fintype α] [DecidableEq α] {L : ℕ} (a : α)
    (w : (Fin (L + 1) → Kind) → (Fin L → Labels α) → ℝ)
    (hw : ∀ τ x, 0 ≤ w τ x) :
    (∑ x : CompatiblePaths α (L := L) a,
      w (fun t => classify (layerLabels a x.1 t)) x.1) ≤
      ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths α a τ, w τ x.1 := by
  rw [sum_compatiblePaths_pairingWeight]
  exact Finset.sum_le_sum (fun τ _ => sum_exactPaths_le_sum_relaxedPaths a τ (w τ) (hw τ))

end Problem335.Pairings

end OAI
