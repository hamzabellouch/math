import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspFourierSurjective
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspRemainder

namespace OAI

/-! The actual nonconstant Eisenstein Fourier series is a continuous
function on its period torus. Its coefficients retain the arithmetic
Dirichlet series and heat integral, including the zero-mode exclusion. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance] Classical.propDecidable

def cubicThetaTorusRemainder (v : ℝ) (s : ℂ) : C(UnitAddTorus (Fin 2),ℂ) :=
  ∑' h : Eisenstein, cubicThetaNonzeroFrequencyTerm (0,v) s h • cubicThetaTorusFourier h

lemma cubicThetaTorusRemainder_summable {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2<s.re) :
    Summable (fun h : Eisenstein => cubicThetaNonzeroFrequencyTerm (0,v) s h • cubicThetaTorusFourier h) := by
  apply Summable.of_norm
  have he := (cubicThetaNonzeroFrequencyTerm_summable (p:=(0,v)) hv hs).norm
  simpa only [norm_smul,cubicThetaTorusFourier,UnitAddTorus.mFourier_norm,mul_one] using he

lemma cubicThetaNonzeroFrequencyTerm_phase (v : ℝ) (s : ℂ) (h : Eisenstein) (z : ℂ) :
    cubicThetaNonzeroFrequencyTerm (0,v) s h*
      (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)=
      cubicThetaNonzeroFrequencyTerm (z,v) s h := by
  by_cases hh : h=0
  · simp [cubicThetaNonzeroFrequencyTerm,hh]
  · simp [cubicThetaNonzeroFrequencyTerm,hh,tracePair]
    ring

lemma cubicThetaTorusRemainder_real {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2<s.re)
    (x : Fin 2 → ℝ) :
    cubicThetaTorusRemainder v s (fun i => (x i:UnitAddCircle))=
      ∑' h : Eisenstein, cubicThetaNonzeroFrequencyTerm (cubicThetaPeriodCell x,v) s h := by
  have he := (ContinuousMap.evalCLM ℂ (fun i => (x i:UnitAddCircle))).map_tsum
    (cubicThetaTorusRemainder_summable hv hs)
  change cubicThetaTorusRemainder v s (fun i => (x i:UnitAddCircle))=_ at he
  rw [he]
  apply tsum_congr
  intro h
  change cubicThetaNonzeroFrequencyTerm (0,v) s h*
    cubicThetaTorusFourier h (fun i => (x i:UnitAddCircle))=_
  rw [cubicThetaTorusFourier_actual,cubicThetaNonzeroFrequencyTerm_phase]

theorem cubicThetaEisenstein_torus {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2<s.re)
    (x : Fin 2 → ℝ) :
    cubicThetaEisenstein (cubicThetaPeriodCell x,v) s=
      cubicThetaEisensteinConstantMode v s+
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
        cubicThetaTorusRemainder v s (fun i => (x i:UnitAddCircle)) := by
  rw [cubicThetaTorusRemainder_real hv hs]
  exact cubicThetaEisenstein_nonzero_coefficients hv hs

lemma cubicThetaTorusFourier_toLp (h : Eisenstein) :
    ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus (Fin 2))) ℂ (cubicThetaTorusFourier h)=cubicThetaTorusBasis h := by
  change UnitAddTorus.mFourierLp 2 (cubicThetaFourierIndex h)=
    UnitAddTorus.mFourierBasis (cubicThetaFourierIndex h)
  exact congrFun UnitAddTorus.coe_mFourierBasis.symm _

theorem cubicThetaTorusRemainder_coefficient {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2<s.re)
    (k : Eisenstein) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus (Fin 2))) ℂ (cubicThetaTorusRemainder v s)) k=
      cubicThetaNonzeroFrequencyTerm (0,v) s k := by
  let L := (cubicThetaTorusCoefficientMap k).comp (ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus (Fin 2))) ℂ)
  rw [← cubicThetaTorusCoefficientMap_apply k]
  change L (cubicThetaTorusRemainder v s)=_
  rw [cubicThetaTorusRemainder,L.map_tsum (cubicThetaTorusRemainder_summable hv hs)]
  rw [tsum_eq_single k]
  · simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,ite_true,smul_eq_mul,mul_one]
  · intro h hne
    simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,
      ite_eq_right hne.symm,smul_zero]

theorem cubicThetaTorusRemainder_mean_zero {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2<s.re) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus (Fin 2))) ℂ (cubicThetaTorusRemainder v s)) 0=0 := by
  rw [cubicThetaTorusRemainder_coefficient hv hs]
  simp [cubicThetaNonzeroFrequencyTerm]

end CubicFirstMoment

end

end OAI
