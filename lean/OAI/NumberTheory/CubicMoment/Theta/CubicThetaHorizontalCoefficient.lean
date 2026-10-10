import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTorusCellIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinTorus

namespace OAI

/-! The exact Fourier coefficient normalization for the physical cusp cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

local instance cubicThetaHorizontalCoefficientMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaHorizontalCoefficientProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma cubicThetaTorusCoefficient_integral (F : C(UnitAddTorus (Fin 2),ℂ))
    (h : Eisenstein) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ F) h=
      ∫ t, star (cubicThetaTorusFourier h t)*F t := by
  unfold cubicThetaTorusCoefficient
  rw [UnitAddTorus.mFourierCoeff_toLp]
  simp only [UnitAddTorus.mFourierCoeff,UnitAddTorus.mFourier_neg,
    starRingEnd_apply,smul_eq_mul,cubicThetaTorusFourier]

lemma cubicThetaHorizontalCoefficient (f : ℂ → ℂ)
    (F : C(UnitAddTorus (Fin 2),ℂ)) (h : Eisenstein)
    (hf : ∀ x, f (cubicThetaPeriodCell x)=F (fun i => (x i:UnitAddCircle))) :
    (∫ z in cubicThetaHorizontalCell,
      star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*f z)=
      (9*Real.sqrt 3/2:ℝ) • cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ F) h := by
  rw [cubicThetaHorizontalCell_integral,cubicThetaTorusCoefficient_integral,
    cubicThetaTorus_integral_cell]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [hf,cubicThetaTorusFourier_actual]

end CubicFirstMoment

end

end OAI
