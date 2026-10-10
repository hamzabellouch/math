import OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeScale

namespace OAI

/-! The canonical prime count and padding degree cap satisfy the numerical
budgets of the trace theorem with an absolute coefficient. -/

namespace TwoPointCorrelations

lemma prime_trace_degree_budget (W L : ℝ) (hW : 1 ≤ W) (hL : 1 ≤ L) :
    ((primeSupplyCount W L + ⌊100 * Real.log L⌋₊ : ℕ) : ℝ) ≤ 101 * Real.log L ∧
      (⌊100 * Real.log L⌋₊ : ℝ) ≤ 100 * Real.log L := by
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hcount := primeSupplyCount_mul_bound W L (by linarith) hL
  have hprod : (primeSupplyCount W L : ℝ) ≤ primeSupplyCount W L * (6 * W) := by
    have hb := mul_le_mul_of_nonneg_left hW (show (0 : ℝ) ≤ primeSupplyCount W L by positivity)
    nlinarith
  have hj : (primeSupplyCount W L : ℝ) ≤ Real.log L := by
    nlinarith
  have hm : (⌊100 * Real.log L⌋₊ : ℝ) ≤ 100 * Real.log L := Nat.floor_le (by positivity)
  refine ⟨?_, hm⟩
  push_cast
  linarith

lemma prime_trace_endpoints (L : ℝ) (hL : 1 ≤ L) :
    1 ≤ ⌊Real.exp L⌋₊ ∧
      (⌊Real.exp L⌋₊ : ℝ) ≤ Real.exp L ∧
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ ⌈Real.exp (L ^ (199 / 200 : ℝ))⌉₊ ∧
      (⌊Real.exp (100 * L + 1)⌋₊ : ℝ) ≤ Real.exp (100 * L + 1) ∧
      (⌊Real.exp (2 * L)⌋₊ : ℝ) ≤ Real.exp (2 * L) := by
  refine ⟨?_, Nat.floor_le (Real.exp_pos _).le, Nat.le_ceil _,
    Nat.floor_le (Real.exp_pos _).le, Nat.floor_le (Real.exp_pos _).le⟩
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  simpa only [Nat.cast_one] using Real.one_le_exp (by linarith : 0 ≤ L)

end TwoPointCorrelations

end OAI
