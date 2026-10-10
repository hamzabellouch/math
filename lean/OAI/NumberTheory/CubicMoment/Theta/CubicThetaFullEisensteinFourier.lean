import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveFourierObservable
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticTorus

namespace OAI

/-! The actual initial Eisenstein Fourier coefficient on every positive
horosphere, including below the injective cusp. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

local instance cubicThetaFullEisensteinFourierMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaFullEisensteinFourierProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def cubicThetaEisensteinSection (s : ℂ) (hs : 2<s.re) : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaEisenstein p.val s,by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (cubicThetaEisenstein_continuousAt hs p.property).comp continuous_subtype_val.continuousAt⟩,by
    intro g p
    exact cubicThetaEisenstein_automorphy g p.property s⟩

def cubicThetaFullTorus (v : ℝ) (s : ℂ) : C(UnitAddTorus (Fin 2),ℂ) :=
  cubicThetaArithmeticTorus v s+(v:ℂ)^s • cubicThetaTorusFourier 0

lemma cubicThetaFullTorus_real {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2<s.re)
    (x : Fin 2 → ℝ) :
    cubicThetaEisenstein (cubicThetaPeriodCell x,v) s=
      cubicThetaFullTorus v s (fun i => (x i:UnitAddCircle)) := by
  rw [cubicThetaEisenstein_torus hv hs]
  simp only [cubicThetaFullTorus,cubicThetaArithmeticTorus,ContinuousMap.add_apply,
    ContinuousMap.smul_apply,cubicThetaTorusFourier_zero,ContinuousMap.one_apply,
    smul_eq_mul,mul_one]
  ring

lemma cubicThetaFullTorus_coefficient {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2<s.re)
    {h : Eisenstein} (hh : h≠0) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ (cubicThetaFullTorus v s)) h=
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
        cubicThetaNonzeroFrequencyTerm (0,v) s h := by
  let L := (cubicThetaTorusCoefficientMap h).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaFullTorus v s)=_
  rw [cubicThetaFullTorus,map_add,map_smul]
  simp only [L,ContinuousLinearMap.comp_apply,cubicThetaTorusCoefficientMap_apply,smul_eq_mul]
  rw [cubicThetaArithmeticTorus_coefficient hv hs hh,cubicThetaTorusFourier_toLp,
    cubicThetaTorusCoefficient_basis,ite_eq_right hh,mul_zero,add_zero]

lemma cubicThetaEisenstein_horizontal_coefficient {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2<s.re) {h : Eisenstein} (hh : h≠0) :
    (∫ z in cubicThetaHorizontalCell,
      star (cubicThetaHorizontalCharacter h z)*cubicThetaEisenstein (z,v) s)=
      (9*Real.sqrt 3/2:ℝ) •
        (((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
          cubicThetaNonzeroFrequencyTerm (0,v) s h) := by
  unfold cubicThetaHorizontalCharacter
  rw [cubicThetaHorizontalCoefficient (fun z => cubicThetaEisenstein (z,v) s)
    (cubicThetaFullTorus v s) h (cubicThetaFullTorus_real hv hs),
    cubicThetaFullTorus_coefficient hv hs hh]

end CubicFirstMoment

end

end OAI
