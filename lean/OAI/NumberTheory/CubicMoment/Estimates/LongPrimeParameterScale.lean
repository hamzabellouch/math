import OAI.NumberTheory.CubicMoment.Estimates.LongPrimeLogScale

namespace OAI

/-! Fixed powers of log X fit the prime parameter log X/4 after a
one-unit exponent enlargement. This is uniform in all arithmetic data. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_log_parameter_power (c A : ℝ) :
    ∀ᶠ X : ℝ in atTop,
      0 < Real.log X/4 ∧ c*(Real.log X)^A ≤ (Real.log X/4)^(A+1) := by
  have ht : Tendsto (fun X : ℝ => Real.log X/4) atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const (by norm_num : (0:ℝ) < 4)
  filter_upwards [ht.eventually (eventually_ge_atTop (max 1 (c*4^A)))] with X hX
  have hT : 0 < Real.log X/4 := zero_lt_one.trans_le ((le_max_left _ _).trans hX)
  refine ⟨hT,?_⟩
  have he : Real.log X = 4*(Real.log X/4) := by ring
  calc
    c*(Real.log X)^A = (c*4^A)*(Real.log X/4)^A := by
      conv_lhs => rw [he,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hT.le]
      ring
    _ ≤ (Real.log X/4)*(Real.log X/4)^A :=
      mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hX) (Real.rpow_nonneg hT.le _)
    _ = (Real.log X/4)^(A+1) := by
      rw [Real.rpow_add hT,Real.rpow_one]
      ring

lemma prime_parameter_log_saving {L D b : ℝ} (hL : 0 < L) :
    b/(L/4)^D = 4^D*b/L^D := by
  rw [Real.div_rpow hL.le (by norm_num : (0:ℝ) ≤ 4)]
  field_simp

end CubicFirstMoment

end

end OAI
