import OAI.Geometry.SurfaceImmersion.Geometry.FiniteParametrix

namespace OAI

/-! Finite parametrix improvement controls amplitudes as well as residuals. -/
noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.FiniteParametrix

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma improve_sub_initial (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E) (j : ℕ) :
    improve A S b z j - z = -∑ i ∈ Finset.range j, S (residual A S b z i) := by
  induction j with
  | zero => simp [improve]
  | succ j ih =>
    rw [Finset.sum_range_succ, neg_add]
    have h := improve_difference A S b z j
    rw [← ih]
    rw [← h]
    abel

lemma improve_sub_initial_bound (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E)
    (p : ℕ → Seminorm ℝ F) (q : ℕ → Seminorm ℝ E) (L : ℕ) (K C B : ℕ → ℝ)
    {η : ℝ} (hη : 0 ≤ η) (hK : ∀ m, 0 ≤ K m) (hB : ∀ m, 0 ≤ B m)
    (hdef : ∀ m f, p m (defect A S f) ≤ η * K m * p (m + L) f)
    (hS : ∀ m f, q m (S f) ≤ B m * p (m + L) f)
    (hinit : ∀ m, p m (A z - b) ≤ C m) (j m : ℕ) :
    q m (improve A S b z j - z) ≤
      ∑ i ∈ Finset.range j, B m * η ^ i * boundProfile L K C i (m + L) := by
  rw [improve_sub_initial, map_neg_eq_map]
  have hsum : q m (∑ i ∈ Finset.range j, S (residual A S b z i)) ≤
      ∑ i ∈ Finset.range j, q m (S (residual A S b z i)) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      exact (map_add_le_add _ _ _).trans (add_le_add ih le_rfl)
  apply hsum.trans
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ B m * p (m + L) (residual A S b z i) := hS m _
    _ ≤ B m * (η ^ i * boundProfile L K C i (m + L)) :=
      mul_le_mul_of_nonneg_left (residual_bound A S b z p L K C hη hK hdef hinit i (m + L)) (hB m)
    _ = _ := by ring

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
