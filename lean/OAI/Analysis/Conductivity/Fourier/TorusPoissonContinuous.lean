import Mathlib
import OAI.Analysis.Conductivity.Fourier.TorusPoissonFlow
import OAI.Analysis.Conductivity.Fourier.TorusFourierSmooth

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance torusPoissonContinuousMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusPoissonContinuousProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma poisson_series_norm_summable {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {t : ℝ} (ht : 0<t) (f : TorusL2) :
    Summable (fun h => ‖((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h) • mFourier h‖) := by
  apply ((torusRate_exp_summable hs ht).mul_left ‖f‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun h => ?_)
  rw [norm_smul,mFourier_norm,mul_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simpa only [mul_comm,neg_mul,mul_neg] using
    mul_le_mul_of_nonneg_left (torusFourierCoeff_bound f h) (Real.exp_nonneg (-torusRate s h*t))

def torusPoissonContinuous (s : Fin 3 → ℝ) (t : ℝ) (f : TorusL2) :
    C(UnitAddTorus (Fin 2),ℂ) :=
  ∑' h, ((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h) • mFourier h

theorem torusPoissonContinuous_toLp {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {t : ℝ} (ht : 0<t) (f : TorusL2) :
    (torusPoissonContinuous s t f).toLp 2 volume ℂ=torusPoissonFlow s t f := by
  have hsum := (poisson_series_norm_summable hs ht f).of_norm.hasSum
  have hm := (ContinuousMap.toLp 2 volume ℂ).hasSum hsum
  have he := hasSum_mFourier_series_L2 (torusPoissonFlow s t f)
  simp only [torusPoissonFlow_coeff,abs_of_pos ht] at he
  apply hm.unique
  convert! he using 1

lemma torusPoissonContinuous_apply {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {t : ℝ} (ht : 0<t) (f : TorusL2) (x : UnitAddTorus (Fin 2)) :
    torusPoissonContinuous s t f x=
      ∑' h, (Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h*mFourier h x := by
  exact ((ContinuousMap.evalCLM ℂ x).hasSum
    (poisson_series_norm_summable hs ht f).of_norm.hasSum).tsum_eq.symm

end

open MeasureTheory Filter Topology UnitAddTorus Real Set
open scoped ENNReal

local instance torusAnglesMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusAnglesProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def torusAngles (x : Fin 3 → ℝ) : UnitAddTorus (Fin 2) :=
  ![(x 1/(2*Real.pi):ℝ),(x 2/(2*Real.pi):ℝ)]

lemma mFourier_torusAngles (h : Fin 2 → ℤ) (x : Fin 3 → ℝ) :
    mFourier h (torusAngles x)=Complex.exp ((torusAngular h x:ℂ)*Complex.I) := by
  simp only [mFourier,ContinuousMap.coe_mk,Fin.prod_univ_two,torusAngles,
    Matrix.cons_val_zero,Matrix.cons_val_one,fourier_coe_apply,
    Complex.ofReal_one,div_one,←Complex.exp_add,torusAngular,add_apply,
    smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

lemma flatFourier_summable {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B)
    {x : Fin 3 → ℝ} (hx : 0<x 0) :
    Summable (fun h => a h*flatPhaseMode s h (phase h) x) := by
  apply Summable.of_norm
  apply ((torusRate_exp_summable hs hx).mul_left B).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro h
  rw [Real.norm_eq_abs,abs_mul,flatPhaseMode,abs_mul,abs_of_pos (exp_pos _)]
  calc
    _ ≤ B*(exp (-torusRate s h*x 0)*1) := mul_le_mul (ha h)
      (mul_le_mul_of_nonneg_left (abs_cos_le_one _) (exp_nonneg _)) (by positivity)
      ((abs_nonneg _).trans (ha h))
    _ = _ := by rw [mul_one]; congr 2; ring

lemma complex_mode_real (c : ℂ) (r θ : ℝ) :
    ((exp r:ℂ)*c*Complex.exp ((θ:ℂ)*Complex.I)).re=
      c.re*(exp r*cos θ)+c.im*(exp r*cos (θ+Real.pi/2)) := by
  rw [Complex.exp_mul_I]
  rw [←Complex.ofReal_cos, ←Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im]
  rw [cos_add_pi_div_two]
  ring

def torusRealContinuation (s : Fin 3 → ℝ) (f : TorusL2) (x : Fin 3 → ℝ) : ℝ :=
  (torusPoissonContinuous s (x 0) f (torusAngles x)).re

lemma torusRealContinuation_eq {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : TorusL2) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    torusRealContinuation s f x=
      flatFourier s (fun h => (mFourierCoeff f h).re) (fun _ => 0) x+
      flatFourier s (fun h => (mFourierCoeff f h).im) (fun _ => Real.pi/2) x := by
  have hre (h) : |(mFourierCoeff f h).re|≤‖f‖ :=
    (Complex.abs_re_le_norm _).trans (torusFourierCoeff_bound f h)
  have him (h) : |(mFourierCoeff f h).im|≤‖f‖ :=
    (Complex.abs_im_le_norm _).trans (torusFourierCoeff_bound f h)
  have hc := (ContinuousMap.evalCLM ℂ (torusAngles x)).hasSum
    (poisson_series_norm_summable hs hx f).of_norm.hasSum
  have hr := Complex.reCLM.hasSum hc
  change HasSum (fun h => ((exp (-torusRate s h*x 0):ℂ)*mFourierCoeff f h*mFourier h (torusAngles x)).re)
    (torusRealContinuation s f x) at hr
  rw [←hr.tsum_eq]
  unfold flatFourier
  rw [←(flatFourier_summable hs hre hx).tsum_add (flatFourier_summable hs him hx)]
  apply tsum_congr
  intro h
  rw [mFourier_torusAngles,complex_mode_real]
  simp only [flatPhaseMode,add_zero]

lemma torusRealContinuation_smooth {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : TorusL2) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (torusRealContinuation s f) {x | 0<x 0} := by
  have hre (h) : |(mFourierCoeff f h).re|≤‖f‖ :=
    (Complex.abs_re_le_norm _).trans (torusFourierCoeff_bound f h)
  have him (h) : |(mFourierCoeff f h).im|≤‖f‖ :=
    (Complex.abs_im_le_norm _).trans (torusFourierCoeff_bound f h)
  exact ((flatFourier_smooth hs hre).add (flatFourier_smooth hs him)).congr
    (fun x hx => torusRealContinuation_eq hs f hx)

end ScalarConductivity

end

end OAI
