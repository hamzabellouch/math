import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerMellin
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

namespace OAI

/-! Absolute Mellin convergence of the fixed cubic Whittaker kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaWhittaker_mellinConvergent {s : ℂ} (hs : 1/6 < s.re) :
    MellinConvergent cubicThetaWhittaker (2*s-1) := by
  have hbase : ((2*Real.pi:ℝ):ℂ)^(-2*s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
  have h1 : Complex.Gamma (s+1/6) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using (show 0 < s.re+1/6 by linarith))
  have h2 : Complex.Gamma (s-1/6) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using (show 0 < s.re-1/6 by linarith))
  have hm : mellin cubicThetaWhittaker (2*s-1) ≠ 0 := by
    rw [cubicThetaWhittaker_mellin hs]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hbase) h1) h2
  by_contra h
  exact hm (integral_undef h)

lemma cubicThetaWhittaker_scaled_mellinConvergent {s : ℂ} (hs : 1/6 < s.re)
    {r : ℝ} (hr : 0 < r) (c : ℂ) :
    MellinConvergent (fun v : ℝ => c*cubicThetaWhittaker (r*v)) (2*s-1) := by
  exact ((MellinConvergent.comp_mul_left hr).mpr
    (cubicThetaWhittaker_mellinConvergent hs)).const_smul c

/-- The norm mass changes by the exact Mellin scaling power. -/
lemma cubicWhittaker_norm_mass_scale (σ : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ v in Ioi (0:ℝ), v^(σ-1)*‖cubicThetaWhittaker (r*v)‖) =
      r^(-σ)*(∫ v in Ioi (0:ℝ), v^(σ-1)*‖cubicThetaWhittaker v‖) := by
  have hcancel : r^(1-σ)*r^(σ-1) = 1 := by
    rw [←Real.rpow_add hr]
    simp
  have he : (∫ v in Ioi (0:ℝ), v^(σ-1)*‖cubicThetaWhittaker (r*v)‖) =
      r^(1-σ)*(∫ v in Ioi (0:ℝ), (r*v)^(σ-1)*‖cubicThetaWhittaker (r*v)‖) := by
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [Real.mul_rpow hr.le hv.le]
    simp only [←mul_assoc,hcancel,one_mul]
  rw [he,integral_comp_mul_left_Ioi (fun v : ℝ => v^(σ-1)*‖cubicThetaWhittaker v‖) 0 hr,mul_zero]
  simp only [smul_eq_mul]
  have hp : r^(1-σ)*r⁻¹ = r^(-σ) := by
    rw [←Real.rpow_neg_one,←Real.rpow_add hr]
    congr 1
    ring
  rw [←mul_assoc,hp]

end CubicFirstMoment

end

end OAI
