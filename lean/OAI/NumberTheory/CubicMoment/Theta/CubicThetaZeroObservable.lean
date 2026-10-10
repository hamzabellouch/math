import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspFourierNormalization

namespace OAI

/-! The genuine zero-frequency observation retains the explicit
arithmetic scattering coefficient. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

local instance cubicThetaZeroObservableMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaZeroObservableProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma cubicThetaArithmeticTorus_zero {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2<s.re) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ (cubicThetaArithmeticTorus v s)) 0=
      cubicThetaEisensteinConstantMode v s-(v:ℂ)^s := by
  let L := (cubicThetaTorusCoefficientMap 0).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [← cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaArithmeticTorus v s)=_
  rw [cubicThetaArithmeticTorus,map_add,map_smul,map_smul]
  simp only [L,ContinuousLinearMap.comp_apply,cubicThetaTorusFourier_toLp,
    cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,ite_true,
    cubicThetaTorusRemainder_mean_zero hv hs,smul_eq_mul,mul_one,mul_zero,add_zero]

lemma cubicThetaArithmetic_horizontal_zero {v : ℝ} (hv : 2≤v)
    {s : ℂ} (hs : 2<s.re) :
    (∫ z in cubicThetaHorizontalCell,
      star (Real.fourierChar (tracePair z (cubicThetaRowFrequency 0)):ℂ)*
        cubicThetaArithmeticRemainder (z,v) s)=
      (9*Real.sqrt 3/2:ℝ) • (cubicThetaEisensteinConstantMode v s-(v:ℂ)^s) := by
  rw [cubicThetaHorizontalCoefficient (fun z => cubicThetaArithmeticRemainder (z,v) s)
    (cubicThetaArithmeticTorus v s) 0 (cubicThetaArithmeticTorus_real hv hs),
    cubicThetaArithmeticTorus_zero (by linarith) hs]

def cubicThetaZeroRadialTest (W : C_c(ℝ,ℂ)) (s : ℂ) : ℂ :=
  ∫ v in Ioi (2:ℝ), star (W v)*(v:ℂ)^(2-s)/(v:ℂ)^3

theorem cubicThetaCuspZeroObservable_normalized (W : C_c(ℝ,ℂ))
    {s : ℂ} (hs : 3<s.re) :
    cubicThetaCuspFourierObservable 0 W s=
      ((Real.pi:ℂ)/(s-1))*cubicThetaConstantContinuation s*cubicThetaZeroRadialTest W s := by
  rw [cubicThetaCuspFourierObservable_iterated 0 W hs,cubicThetaZeroRadialTest,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  change 2<v at hv
  dsimp only
  rw [cubicThetaArithmetic_horizontal_zero hv.le (by linarith),
    cubicThetaEisensteinConstantMode_eq (by linarith) (by linarith),
    add_sub_cancel_left,cubicThetaConstantContinuation_right (by linarith),Complex.real_smul]
  calc
    _ = (((9*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(9*Real.sqrt 3):ℂ))/(s-1)*
        cubicThetaConstantContinuation s*(star (W v)*(v:ℂ)^(2-s)/(v:ℂ)^3) := by ring
    _ = _ := by rw [cubicThetaPeriod_fourier_constant]

end CubicFirstMoment

end

end OAI
