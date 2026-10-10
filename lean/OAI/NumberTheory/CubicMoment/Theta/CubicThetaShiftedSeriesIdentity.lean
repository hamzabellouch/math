import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedSeriesFunction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaContinuousFourierSeparation

namespace OAI

/-! Reconstruction of the actual translated-cusp section from its computed
coefficients. The nontrivial cusp has no constant mode. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma cubicThetaShiftedCell_integral_scaled (f : ℂ → ℂ) :
    (∫ z in cubicThetaShiftedHorizontalCell,f z)=
      (9:ℝ) • ∫ z in cubicThetaHorizontalCell,f (3*z) := by
  rw [cubicThetaShiftedHorizontalCell_integral,cubicThetaHorizontalCell_integral,smul_smul]
  congr 1
  ring

lemma cubicThetaShiftedModelHorizontal_term (m n : ℤ) (hn : ¬(3:ℤ) ∣ n)
    {v : ℝ} (hv : 1<v) (h : Eisenstein) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v=
      (81*Real.sqrt 3/2:ℝ) • cubicThetaShiftedModelTerm n v h := by
  by_cases hh : h=0
  · subst h
    rw [cubicThetaShiftedConstantCoefficient_nontrivial m n hn hv]
    simp only [cubicThetaShiftedModelTerm,ite_true,smul_zero]
  · have hc : (((81*Real.sqrt 3/2:ℝ):ℂ))≠0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
    rw [cubicThetaShiftedCoefficient_whittaker m n hh hv]
    simp only [cubicThetaShiftedModelTerm,ite_eq_right hh,
      cubicThetaShiftedNormalizedCoefficient,Complex.real_smul]
    field_simp

lemma cubicThetaShiftedModelSeries_coefficient (n : ℤ) {v : ℝ} (hv : 0<v) (h : Eisenstein) :
    (∫ z in cubicThetaShiftedHorizontalCell,
      star (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)*
        cubicThetaShiftedModelSeries n z v)=
      (81*Real.sqrt 3/2:ℝ) • cubicThetaShiftedModelTerm n v h := by
  rw [cubicThetaShiftedHorizontalCoefficient _ (cubicThetaShiftedModelTorus n v) h
    (fun x => (cubicThetaShiftedModelTorus_real n hv x).symm),
    cubicThetaShiftedModelTorus_coefficient n hv]

theorem cubicThetaShiftedSeriesIdentity (m n : ℤ) (hn : ¬(3:ℤ) ∣ n)
    {v : ℝ} (hv : 1<v) (z : ℂ) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex
        (cubicThetaShiftedInversion ((m:Eisenstein)+n*omegaE))) (z,v))=
      cubicThetaShiftedModelSeries n z v := by
  have hv0 : 0<v := lt_trans (show (0:ℝ)<1 by norm_num) hv
  have hf := cubicThetaContinuousFourier_ext
    (cubicThetaShifted_actual_continuous ((m:Eisenstein)+n*omegaE) hv0)
    (cubicThetaShiftedModelSeries_continuous n hv0)
    (fun a w => cubicThetaShifted_actual_periodic _ a hv0 w)
    (fun a w => cubicThetaShiftedModelSeries_periodic n v a w) (fun h => by
      have he := (cubicThetaShiftedModelHorizontal_term m n hn hv h).trans
        (cubicThetaShiftedModelSeries_coefficient n hv0 h).symm
      unfold cubicThetaShiftedModelHorizontal at he
      rw [cubicThetaShiftedCell_integral_scaled,cubicThetaShiftedCell_integral_scaled] at he
      simp only [cubicThetaShifted_phase_tripled,cubicThetaHorizontalCharacter,
        Complex.real_smul,Complex.ofReal_ofNat] at he
      exact mul_left_cancel₀ (by norm_num : (9:ℂ)≠0) he)
  have he := congrFun hf (z/3)
  simpa only [show 3*(z/3)=z by ring] using he

end CubicFirstMoment

end

end OAI
