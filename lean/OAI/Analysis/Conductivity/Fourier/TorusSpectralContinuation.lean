import Mathlib
import OAI.Analysis.Conductivity.Flux.TorusCylinderGreenReal

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

lemma torusSpectralSynthesis_coeff (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (h : Fin 2 → ℤ) :
    mFourierCoeff (torusSpectralSynthesis s f) h=f.val 0 h := by
  rw [←mFourierBasis_repr]
  change (mFourierBasis (d:=Fin 2)).repr ((mFourierBasis (d:=Fin 2)).repr.symm (f.val 0)) h=_
  rw [LinearIsometryEquiv.apply_symm_apply]

lemma torusRealContinuation_spectral {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) {x : Coord3} (hx : 0<x 0) :
    torusRealContinuation s (torusSpectralSynthesis s f) x=
      (endPoissonField s f 0 (x 0,torusAngles x)).re := by
  unfold torusRealContinuation
  congr 1
  rw [torusPoissonContinuous_apply hs hx]
  unfold endPoissonField
  apply tsum_congr
  intro h
  simp [endPoissonModeField,endModeCoefficient,torusSpectralSynthesis_coeff]

lemma mFourierCoeff_Lp_add (f g : TorusL2) (h : Fin 2 → ℤ) :
    mFourierCoeff (f+g) h=mFourierCoeff f h+mFourierCoeff g h := by
  simp only [←mFourierBasis_repr,map_add,lp.coeFn_add,Pi.add_apply]

lemma mFourierCoeff_Lp_neg (f : TorusL2) (h : Fin 2 → ℤ) :
    mFourierCoeff (-f) h= -mFourierCoeff f h := by
  simp only [←mFourierBasis_repr,map_neg,lp.coeFn_neg,Pi.neg_apply]

lemma torusPoissonContinuous_add {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {t : ℝ} (ht : 0<t) (f g : TorusL2) :
    torusPoissonContinuous s t (f+g)=torusPoissonContinuous s t f+torusPoissonContinuous s t g := by
  unfold torusPoissonContinuous
  simp only [mFourierCoeff_Lp_add,mul_add]
  calc
    _ = ∑' h, (((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h) • mFourier h+
        ((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff g h) • mFourier h) := by
      apply tsum_congr
      intro h
      exact _root_.add_smul (((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h))
        (((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff g h)) (mFourier h)
    _ = _ := (poisson_series_norm_summable hs ht f).of_norm.tsum_add
      (poisson_series_norm_summable hs ht g).of_norm

lemma torusPoissonContinuous_neg (s : Fin 3 → ℝ) (t : ℝ) (f : TorusL2) :
    torusPoissonContinuous s t (-f)= -torusPoissonContinuous s t f := by
  unfold torusPoissonContinuous
  simp only [mFourierCoeff_Lp_neg,mul_neg]
  calc
    _ = ∑' h, - (((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h) • mFourier h) := by
      apply tsum_congr
      intro h
      exact _root_.neg_smul (((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h)) (mFourier h)
    _ = _ := tsum_neg

lemma torusRealContinuation_add {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f g : TorusL2) {x : Coord3} (hx : 0<x 0) :
    torusRealContinuation s (f+g) x=torusRealContinuation s f x+torusRealContinuation s g x := by
  simp only [torusRealContinuation,torusPoissonContinuous_add hs hx,
    ContinuousMap.add_apply,Complex.add_re]

lemma torusRealContinuation_neg (s : Fin 3 → ℝ) (f : TorusL2) (x : Coord3) :
    torusRealContinuation s (-f) x= -torusRealContinuation s f x := by
  simp only [torusRealContinuation,torusPoissonContinuous_neg,ContinuousMap.neg_apply,Complex.neg_re]

lemma torusRealContinuation_sub {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f g : TorusL2) {x : Coord3} (hx : 0<x 0) :
    torusRealContinuation s (f-g) x=torusRealContinuation s f x-torusRealContinuation s g x := by
  simp only [sub_eq_add_neg,torusRealContinuation_add hs f (-g) hx,torusRealContinuation_neg]

end ScalarConductivity

end
end

end OAI
