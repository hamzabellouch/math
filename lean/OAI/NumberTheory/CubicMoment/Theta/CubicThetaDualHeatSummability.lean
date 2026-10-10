import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDualHeatBounds
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowGaussBounds

namespace OAI

/-! Absolute summation of the integrated Fourier heat modes. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaDualHeat_mass_summable {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) :
    Summable (fun h : Eisenstein => ∫ t in Ioi (0:ℝ),
      ‖cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t‖) := by
  let b : ℝ := 4*Real.pi^2/27
  have hb : 0 < b := by dsimp [b]; positivity
  let J : ℝ := Real.Gamma (s.re+1)*(v^2)^(-(s.re+1))
  have hJ : 0 ≤ J := by
    apply mul_nonneg (Real.Gamma_pos_of_pos (by linarith)).le
    exact Real.rpow_nonneg (sq_nonneg v) _
  let K : ℝ := (2/b^2)*J
  have hK : 0 ≤ K := mul_nonneg (by positivity) hJ
  let m0 : ℝ := ∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat v s 0 t‖
  have hm0 : 0 ≤ m0 := integral_nonneg (fun _ => _root_.norm_nonneg _)
  have ht := (hasSum_ite_eq (0:Eisenstein) m0).summable.add
    ((summable_eisenstein_norm_rpow (s := 2) (by norm_num)).mul_left K)
  apply ht.of_nonneg_of_le
  · intro h
    exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  · intro h
    by_cases hh : h = 0
    · subst h
      simp only [cubicThetaRowHeatScale_zero, ite_true]
      exact le_add_of_nonneg_right (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _))
    · simp only [hh, ite_false, zero_add]
      apply (cubicThetaDualHeat_norm_mass_bound hv hs (cubicThetaRowHeatScale_pos hh)).trans_eq
      rw [cubicThetaRowHeatScale_eq]
      change (2/(b*norm h)^2)*J = K*(norm h)^(-(2:ℝ))
      rw [Real.rpow_neg (norm_nonneg h), Real.rpow_two]
      dsimp [K]
      ring

theorem cubicThetaWeightedDualHeat_mass_summable {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) {c : Eisenstein} (hc : c ≠ 0) (z : ℂ) :
    Summable (fun h : Eisenstein => ∫ t in Ioi (0:ℝ),
      ‖(cubicThetaEisensteinGaussCoefficient c h*
        (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ))*
          cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t‖) := by
  have ht := (cubicThetaDualHeat_mass_summable hv hs).mul_left
    (Nat.card (Residues (3*c)):ℝ)
  apply ht.of_nonneg_of_le
  · intro h
    exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  · intro h
    simp_rw [norm_mul, Circle.norm_coe, mul_one]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_right (cubicThetaEisensteinGaussCoefficient_norm hc h)
      (integral_nonneg (fun _ => _root_.norm_nonneg _))

end CubicFirstMoment

end

end OAI
