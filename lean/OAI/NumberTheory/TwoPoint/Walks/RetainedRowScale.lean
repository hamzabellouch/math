import OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeScale
import OAI.NumberTheory.TwoPoint.Walks.ForestCodeAsymptotics

namespace OAI

/-! At a fixed W the retained row majorant grows polynomially in L;
it can therefore be absorbed into a small exponential boundary budget. -/

namespace TwoPointCorrelations

open Filter

lemma primeSupplyCount_le_log (W L : ℝ) (hW : 1 ≤ W) (hL : 1 ≤ L) :
    (primeSupplyCount W L : ℝ) ≤ Real.log L := by
  have hb := primeSupplyCount_mul_bound W L (by linarith) hL
  have hJ : 0 ≤ (primeSupplyCount W L : ℝ) := Nat.cast_nonneg _
  nlinarith [Real.log_nonneg hL]

lemma retained_row_exponential_bound (W L : ℝ) (hW : 1 ≤ W) (hL : 1 ≤ L) :
    Real.exp (4 * primeSupplyCount W L) / L *
        (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ primeSupplyCount W L ≤
      Real.exp ((4 + 400 * Real.log 5 + Real.log (8 * W)) * Real.log L) := by
  have hLp : 0 < L := by linarith
  have hJ := primeSupplyCount_le_log W L hW hL
  have h8 : 1 ≤ 8 * W := by linarith
  have he : Real.exp (4 * primeSupplyCount W L) ≤ Real.exp (4 * Real.log L) :=
    Real.exp_le_exp.mpr (by linarith)
  have hp : (8 * W) ^ primeSupplyCount W L ≤ Real.exp (Real.log (8 * W) * Real.log L) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hJ (Real.log_nonneg h8))
  have h5 : (5 : ℝ) ^ (400 * Real.log L) = Real.exp ((400 * Real.log 5) * Real.log L) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  calc
    _ ≤ Real.exp (4 * primeSupplyCount W L) *
        (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ primeSupplyCount W L := by
      gcongr
      exact div_le_self (Real.exp_pos _).le hL
    _ ≤ Real.exp (4 * Real.log L) *
        Real.exp ((400 * Real.log 5) * Real.log L) *
        Real.exp (Real.log (8 * W) * Real.log L) := by
      rw [h5]
      gcongr
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

lemma eventually_retained_row_scale (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (4 * primeSupplyCount W L) / L *
        (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ primeSupplyCount W L ≤
          Real.exp (L / 4) := by
  let C := 4 + 400 * Real.log 5 + Real.log (8 * W)
  have hC : 0 ≤ C := by
    have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    have h8 : 0 ≤ Real.log (8 * W) := Real.log_nonneg (by linarith)
    dsimp [C]
    linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_sublinear_log_cost 0 (4 * C) (by norm_num) (by positivity)] with L hL hb
  simp only [Real.rpow_zero, mul_one] at hb
  exact (retained_row_exponential_bound W L hW hL).trans
    (Real.exp_le_exp.mpr (by dsimp only [C] at hb ⊢; linarith))

lemma eventually_const_le_exp_quarter (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, C ≤ Real.exp (L / 4) := by
  filter_upwards [eventually_ge_atTop (4 * |C|)] with L hL
  have ha := le_abs_self C
  have he := Real.add_one_le_exp (L / 4)
  linarith

end TwoPointCorrelations

end OAI
