import OAI.NumberTheory.TwoPoint.Bounds.GoodMomentConstant

namespace OAI

/-! Absorb the exact good designated-word cost, including all designations, into the moment base. -/

namespace TwoPointCorrelations

open Filter

theorem eventually_good_trace_cost (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (J k S : ℕ) (K M : ℝ),
      1 ≤ J → L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L →
      (S : ℝ) ≤ L ^ (1 / 4 : ℝ) → 0 ≤ K →
      M ≤ (2 : ℝ) ^ (2 * S) *
        ((Fintype.card (BudgetColumnArrayCode J (4 * k) L) : ℝ) *
          K ^ (2 * k) * (2 * W) ^ (J * k + S)) →
      Real.exp (108 * L) * (2 : ℝ) ^ (4 * k * J) * M ≤
        (K * (Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_budget_column_array_card,
    eventually_good_moment_with_padding W hW] with L hL hcard hmoment
  intro J k S K M hJ hklo hkhi hS hK hM
  have hk : 1 ≤ k := by
    by_contra hn
    have hz : k = 0 := by omega
    subst k
    norm_num at hklo
    linarith
  have hc := hcard k J (4 * k) hklo hkhi (by omega) le_rfl
  have hb : M ≤ (2 : ℝ) ^ (2 * S) *
      (Real.exp (64 * k * J) * K ^ (2 * k) * (2 * W) ^ (J * k + S)) := by
    apply hM.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hc (pow_nonneg hK _)
  calc
    _ ≤ Real.exp (108 * L) * (2 : ℝ) ^ (4 * k * J) *
        ((2 : ℝ) ^ (2 * S) *
          (Real.exp (64 * k * J) * K ^ (2 * k) * (2 * W) ^ (J * k + S))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = Real.exp (108 * L) * (2 : ℝ) ^ (4 * k * J + 2 * S) *
        Real.exp (64 * k * J) * K ^ (2 * k) * (2 * W) ^ (J * k + S) := by
      rw [pow_add]
      ring
    _ ≤ _ := hmoment J k S K hJ hklo hS hK

end TwoPointCorrelations

end OAI
