import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedPositivePointwise
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedPositiveConstant
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedSeriesIdentity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedLattice

namespace OAI

/-! Full translated-cusp expansions at every positive height. The incoming
correction has disappeared on taking the actual spectral residue. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaShiftedPositiveCoefficient_whittaker (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    {v : ℝ} (hv : 0<v) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v=
      (cubicThetaShiftedResidueFactor n h*
        ((2*(cubicThetaShiftedRowHeatScale h)^(1/6:ℝ)/‖cubicThetaShiftedRowFrequency h‖:ℝ):ℂ))*
        cubicThetaWhittaker (‖cubicThetaShiftedRowFrequency h‖*v) := by
  rw [cubicThetaShiftedPositiveCoefficient_pointwise m n hh hv,cubicThetaShiftedPoleRadial,
    cubicThetaShiftedPoleHeat_whittaker hh hv]
  ring

lemma cubicThetaShiftedModelHorizontal_positive_term (m n : ℤ) (hn : ¬(3:ℤ) ∣ n)
    {v : ℝ} (hv : 0<v) (h : Eisenstein) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v=
      (81*Real.sqrt 3/2:ℝ) • cubicThetaShiftedModelTerm n v h := by
  by_cases hh : h=0
  · subst h
    rw [cubicThetaShiftedPositiveConstantCoefficient_nontrivial m n hn hv]
    simp only [cubicThetaShiftedModelTerm,ite_true,smul_zero]
  · have hc : (((81*Real.sqrt 3/2:ℝ):ℂ))≠0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
    rw [cubicThetaShiftedPositiveCoefficient_whittaker m n hh hv]
    simp only [cubicThetaShiftedModelTerm,ite_eq_right hh,
      cubicThetaShiftedNormalizedCoefficient,Complex.real_smul]
    field_simp

theorem cubicThetaShiftedPositiveSeriesIdentity (m n : ℤ) (hn : ¬(3:ℤ) ∣ n)
    {v : ℝ} (hv : 0<v) (z : ℂ) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex
        (cubicThetaShiftedInversion ((m:Eisenstein)+n*omegaE))) (z,v))=
      cubicThetaShiftedModelSeries n z v := by
  have hf := cubicThetaContinuousFourier_ext
    (cubicThetaShifted_actual_continuous ((m:Eisenstein)+n*omegaE) hv)
    (cubicThetaShiftedModelSeries_continuous n hv)
    (fun a w => cubicThetaShifted_actual_periodic _ a hv w)
    (fun a w => cubicThetaShiftedModelSeries_periodic n v a w) (fun h => by
      have he := (cubicThetaShiftedModelHorizontal_positive_term m n hn hv h).trans
        (cubicThetaShiftedModelSeries_coefficient n hv h).symm
      unfold cubicThetaShiftedModelHorizontal at he
      rw [cubicThetaShiftedCell_integral_scaled,cubicThetaShiftedCell_integral_scaled] at he
      simp only [cubicThetaShifted_phase_tripled,cubicThetaHorizontalCharacter,
        Complex.real_smul,Complex.ofReal_ofNat] at he
      exact mul_left_cancel₀ (by norm_num : (9:ℂ)≠0) he)
  have he := congrFun hf (z/3)
  simpa only [show 3*(z/3)=z by ring] using he

theorem cubicThetaShiftedPositiveSeries_common (m n : ℤ) (hn : ¬(3:ℤ) ∣ n)
    {v : ℝ} (hv : 0<v) (z : ℂ) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex
        (cubicThetaShiftedInversion ((m:Eisenstein)+n*omegaE))) (z,v))=
      cubicThetaArithmeticBaseScalar*
        cubicThetaNonconstant (cubicThetaShiftedLatticeCoefficient n) (z,v) := by
  rw [cubicThetaShiftedPositiveSeriesIdentity m n hn hv,cubicThetaShiftedModelSeries_common]

end CubicFirstMoment

end

end OAI
