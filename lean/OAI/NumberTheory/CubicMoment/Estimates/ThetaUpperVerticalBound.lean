import OAI.NumberTheory.CubicMoment.Estimates.ThetaMellinSplit

namespace OAI

/-! Uniform vertical bounds for upper Mellin integrals from one real moment. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def thetaUpperNormMass (f : ℝ→ℂ) (b : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, ‖(t:ℂ)^((b:ℂ)-1) • thetaUpper f t‖

lemma thetaUpperNormMass_nonneg (f : ℝ→ℂ) (b : ℝ) : 0≤thetaUpperNormMass f b :=
  integral_nonneg (fun _ => _root_.norm_nonneg _)

theorem thetaUpper_vertical_bound {f : ℝ→ℂ} {b : ℝ}
    (hf : MellinConvergent (thetaUpper f) (b:ℂ)) {s : ℂ} (hs : s.re≤b) :
    ‖mellin (thetaUpper f) s‖≤thetaUpperNormMass f b := by
  unfold mellin thetaUpperNormMass
  apply norm_integral_le_of_norm_le hf.norm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0<t at ht
  by_cases ht1 : 1<t
  · rw [norm_smul,norm_smul,Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp only [Complex.sub_re,Complex.one_re,Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le ht1.le (sub_le_sub_right hs 1)) (_root_.norm_nonneg _)
  · simp only [thetaUpper,indicator_of_notMem (show t∉Ioi (1:ℝ) from ht1),smul_zero,norm_zero,le_refl]

end CubicFirstMoment

end

end OAI
