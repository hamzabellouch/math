import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalCoefficient
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticRemainder

namespace OAI

/-! The literal arithmetic remainder on each high-cusp torus, with its
nonzero coefficient computed from the initial arithmetic series. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

local instance cubicThetaArithmeticTorusMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaArithmeticTorusProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma cubicThetaFourierIndex_zero : cubicThetaFourierIndex 0=0 := by
  apply (dualIntegerEquiv.trans coordinatesEquiv.toEquiv).injective
  unfold cubicThetaFourierIndex
  rw [Equiv.apply_symm_apply]
  change (0 : Eisenstein)=coordinatesEquiv (dualIntegerEquiv 0)
  have he : dualIntegerEquiv 0=0 := by ext i; fin_cases i <;> simp [dualIntegerEquiv]
  rw [he,map_zero]

lemma cubicThetaTorusFourier_zero : cubicThetaTorusFourier 0=1 := by
  rw [cubicThetaTorusFourier,cubicThetaFourierIndex_zero,UnitAddTorus.mFourier_zero]

def cubicThetaArithmeticTorus (v : ℝ) (s : ℂ) : C(UnitAddTorus (Fin 2),ℂ) :=
  (cubicThetaEisensteinConstantMode v s-(v:ℂ)^s) • cubicThetaTorusFourier 0+
    ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s) •
      cubicThetaTorusRemainder v s

lemma cubicThetaArithmeticTorus_real {v : ℝ} (hv : 2≤v) {s : ℂ} (hs : 2<s.re)
    (x : Fin 2 → ℝ) :
    cubicThetaArithmeticRemainder (cubicThetaPeriodCell x,v) s=
      cubicThetaArithmeticTorus v s (fun i => (x i:UnitAddCircle)) := by
  rw [cubicThetaArithmeticRemainder,
    cubicThetaIncomingEisenstein_high (by linarith : 1<v),cubicThetaCuspCutoff_one hv,
    one_mul,cubicThetaEisenstein_torus (by linarith) hs]
  simp only [cubicThetaArithmeticTorus,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    cubicThetaTorusFourier_zero,ContinuousMap.one_apply,smul_eq_mul,mul_one]
  ring

lemma cubicThetaArithmeticTorus_coefficient {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2<s.re)
    {h : Eisenstein} (hh : h≠0) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ (cubicThetaArithmeticTorus v s)) h=
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
        cubicThetaNonzeroFrequencyTerm (0,v) s h := by
  let L := (cubicThetaTorusCoefficientMap h).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [← cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaArithmeticTorus v s)=_
  rw [cubicThetaArithmeticTorus,map_add,map_smul,map_smul]
  simp only [L,ContinuousLinearMap.comp_apply,cubicThetaTorusFourier_toLp,
    cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,
    ite_eq_right hh,cubicThetaTorusRemainder_coefficient hv hs,smul_eq_mul,mul_zero,zero_add]

lemma cubicThetaArithmetic_horizontal_coefficient {v : ℝ} (hv : 2≤v)
    {s : ℂ} (hs : 2<s.re) {h : Eisenstein} (hh : h≠0) :
    (∫ z in cubicThetaHorizontalCell,
      star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
        cubicThetaArithmeticRemainder (z,v) s)=
      (9*Real.sqrt 3/2:ℝ) •
        (((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
          cubicThetaNonzeroFrequencyTerm (0,v) s h) := by
  rw [cubicThetaHorizontalCoefficient (fun z => cubicThetaArithmeticRemainder (z,v) s)
    (cubicThetaArithmeticTorus v s) h (cubicThetaArithmeticTorus_real hv hs),
    cubicThetaArithmeticTorus_coefficient (by linarith) hs hh]

end CubicFirstMoment

end

end OAI
