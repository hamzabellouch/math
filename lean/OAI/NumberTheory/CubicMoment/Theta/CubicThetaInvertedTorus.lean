import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedCoefficients
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalCoefficient
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticTorus

namespace OAI

/-! The continuous inverted-cusp Fourier series and its physical mean.
The constant term is obtained by an actual torus projection. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment
local instance cubicThetaInvertedTorusMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaInvertedTorusProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance] Classical.propDecidable

def cubicThetaInvertedTorusRemainder (v : ℝ) (s : ℂ) : C(UnitAddTorus (Fin 2),ℂ) :=
  ∑' h : Eisenstein, cubicThetaInvertedNonzeroTerm (0,v) s h • cubicThetaTorusFourier h

lemma cubicThetaInvertedTorusRemainder_summable {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2<s.re) :
    Summable (fun h : Eisenstein =>
      cubicThetaInvertedNonzeroTerm (0,v) s h • cubicThetaTorusFourier h) := by
  apply Summable.of_norm
  have he := (cubicThetaInvertedNonzeroTerm_summable (p:=(0,v)) hv hs).norm
  simpa only [norm_smul,cubicThetaTorusFourier,UnitAddTorus.mFourier_norm,mul_one] using he

lemma cubicThetaInvertedNonzeroTerm_phase (v : ℝ) (s : ℂ) (h : Eisenstein) (z : ℂ) :
    cubicThetaInvertedNonzeroTerm (0,v) s h*
      (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)=
      cubicThetaInvertedNonzeroTerm (z,v) s h := by
  by_cases hh : h=0
  · simp [cubicThetaInvertedNonzeroTerm,hh]
  · simp [cubicThetaInvertedNonzeroTerm,hh,tracePair]
    ring

lemma cubicThetaInvertedTorusRemainder_real {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2<s.re) (x : Fin 2 → ℝ) :
    cubicThetaInvertedTorusRemainder v s (fun i => (x i:UnitAddCircle))=
      ∑' h : Eisenstein, cubicThetaInvertedNonzeroTerm (cubicThetaPeriodCell x,v) s h := by
  have he := (ContinuousMap.evalCLM ℂ (fun i => (x i:UnitAddCircle))).map_tsum
    (cubicThetaInvertedTorusRemainder_summable hv hs)
  change cubicThetaInvertedTorusRemainder v s (fun i => (x i:UnitAddCircle))=_ at he
  rw [he]
  apply tsum_congr
  intro h
  change cubicThetaInvertedNonzeroTerm (0,v) s h*
    cubicThetaTorusFourier h (fun i => (x i:UnitAddCircle))=_
  rw [cubicThetaTorusFourier_actual,cubicThetaInvertedNonzeroTerm_phase]

lemma cubicThetaInvertedTorusRemainder_coefficient {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2<s.re) (k : Eisenstein) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ
      (cubicThetaInvertedTorusRemainder v s)) k=cubicThetaInvertedNonzeroTerm (0,v) s k := by
  let L := (cubicThetaTorusCoefficientMap k).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply k]
  change L (cubicThetaInvertedTorusRemainder v s)=_
  rw [cubicThetaInvertedTorusRemainder,L.map_tsum (cubicThetaInvertedTorusRemainder_summable hv hs)]
  rw [tsum_eq_single k]
  · simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,ite_true,smul_eq_mul,mul_one]
  · intro h hne
    simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,
      ite_eq_right hne.symm,smul_zero]

def cubicThetaInvertedTorus (v : ℝ) (s : ℂ) : C(UnitAddTorus (Fin 2),ℂ) :=
  cubicThetaInvertedConstantMode v s • cubicThetaTorusFourier 0+
    ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s) •
      cubicThetaInvertedTorusRemainder v s

lemma cubicThetaInvertedTorus_real {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2<s.re) (x : Fin 2 → ℝ) :
    cubicThetaInvertedTorus v s (fun i => (x i:UnitAddCircle))=
      cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion)
        (cubicThetaPeriodCell x,v)) s := by
  rw [cubicThetaEisenstein_inverted_nonzero hv hs]
  simp only [cubicThetaInvertedTorus,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    cubicThetaTorusFourier_zero,ContinuousMap.one_apply,smul_eq_mul,mul_one,
    cubicThetaInvertedTorusRemainder_real hv hs]

lemma cubicThetaInvertedTorus_mean {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2<s.re) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ (cubicThetaInvertedTorus v s)) 0=
      cubicThetaInvertedConstantMode v s := by
  let L := (cubicThetaTorusCoefficientMap 0).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaInvertedTorus v s)=_
  rw [cubicThetaInvertedTorus,map_add,map_smul,map_smul]
  simp only [L,ContinuousLinearMap.comp_apply,cubicThetaTorusFourier_toLp,
    cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,ite_true,
    cubicThetaInvertedTorusRemainder_coefficient hv hs,cubicThetaInvertedNonzeroTerm,
    smul_eq_mul,mul_one,mul_zero,add_zero]

theorem cubicThetaInverted_horizontal_mean {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2<s.re) :
    (∫ z in cubicThetaHorizontalCell, cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (z,v)) s)=
      (9*Real.sqrt 3/2:ℝ) • cubicThetaInvertedConstantMode v s := by
  have he := cubicThetaHorizontalCoefficient
    (fun z => cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (z,v)) s)
    (cubicThetaInvertedTorus v s) 0 (fun x => (cubicThetaInvertedTorus_real hv hs x).symm)
  rw [cubicThetaInvertedTorus_mean hv hs] at he
  simpa [cubicThetaRowFrequency,tracePair] using he

end CubicFirstMoment

end

end OAI
