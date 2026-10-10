import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.DyadicAnnuli

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem dyadic_tail_coefficient (n k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ((ε * 2 ^ k) ^ (n + 1))⁻¹ * (C * (ε * 2 ^ (k + 1)) ^ n) =
      (C * 2 ^ n / ε) * (1 / 2 : ℝ) ^ k := by
  have hr : ε * (2 : ℝ) ^ k ≠ 0 := by positivity
  calc
    _ = C * 2 ^ n / (ε * 2 ^ k) := by
      rw [show ε * (2 : ℝ) ^ (k + 1) = (ε * 2 ^ k) * 2 by rw [pow_succ]; ring,
        mul_pow, pow_succ]
      field_simp
      simp only [mul_pow, pow_succ]
      ring
    _ = _ := by
      rw [div_pow, one_pow]
      field_simp

theorem inverseDistancePow_annular_integral_bound {d : ℕ} (n : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    (∫ y in dyadicAnnulus x ε k, ‖inverseDistancePow (n + 1) x y‖ ∂μ) ≤
      (C * 2 ^ n / ε) * (1 / 2 : ℝ) ^ k := by
  have hfinite := dyadicAnnulus_measure_lt_top n C μ hg x ε hε k
  have hmeasure : μ.real (dyadicAnnulus x ε k) ≤ C * (ε * 2 ^ (k + 1)) ^ n :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (by positivity))
      ((measure_mono (dyadicAnnulus_subset_ball x ε k)).trans
        (hg.2 x _ (by positivity)))
  calc
    _ = ‖∫ y in dyadicAnnulus x ε k, ‖inverseDistancePow (n + 1) x y‖ ∂μ‖ :=
      (Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)).symm
    _ ≤ ((ε * 2 ^ k) ^ (n + 1))⁻¹ * μ.real (dyadicAnnulus x ε k) :=
      norm_setIntegral_le_of_norm_le_const hfinite fun y hy => by
        rw [norm_norm]
        exact inverseDistancePow_bound_on_annulus (n + 1) x ε hε k y hy
    _ ≤ ((ε * 2 ^ k) ^ (n + 1))⁻¹ * (C * (ε * 2 ^ (k + 1)) ^ n) :=
      mul_le_mul_of_nonneg_left hmeasure (by positivity)
    _ = _ := dyadic_tail_coefficient n k C ε hε

theorem inverseDistancePow_integrableOn_exterior {d : ℕ} (n : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (inverseDistancePow (n + 1) x) {y | ε < dist x y} μ := by
  have hgeo : Summable (fun k : ℕ => (C * 2 ^ n / ε) * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  have hs : Summable (fun k : ℕ =>
      ∫ y in dyadicAnnulus x ε k, ‖inverseDistancePow (n + 1) x y‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _)
      (fun k => inverseDistancePow_annular_integral_bound n C μ hg x ε hε k) hgeo
  exact (integrableOn_iUnion_of_summable_integral_norm
    (fun k => inverseDistancePow_integrableOn_annulus n (n + 1) C μ hg x ε hε k) hs).mono_set
      (exterior_subset_iUnion_dyadicAnnulus x ε hε)

end

end RieszRectifiability

end OAI
