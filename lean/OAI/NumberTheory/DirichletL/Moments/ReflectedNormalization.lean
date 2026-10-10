import OAI.NumberTheory.DirichletL.Moments.OneReflectionEnergy
import OAI.NumberTheory.DirichletL.Moments.ReflectedAnnuli

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentReflectedNormalization
open HeckeFamily CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open EisensteinSchwartzPoisson

lemma actual_log_window :
    CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow=
      (fun x : ℝ=>(annulus x:ℂ)) := by
  funext x
  unfold CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow
  split_ifs with hx
  · rw [Real.exp_log hx]
  · rw [annulus_zero_low x (by linarith)]
    rfl

lemma polynomial_const (χ : Character) (W : ℝ→ℂ) (X : ℝ) (c : ℂ) :
    HeckeDyadic.polynomial χ false (fun x=>c*W x) X 0 0=
      c*HeckeDyadic.polynomial χ false W X 0 0 := by
  unfold HeckeDyadic.polynomial
  have he (I : HeckeDyadic.NonzeroIdeal) :
      HeckeDyadic.summand χ false (fun x=>c*W x) X 0 0 I=
        c*HeckeDyadic.summand χ false W X 0 0 I := by
    unfold HeckeDyadic.summand
    ring
  simp_rw [he,tsum_mul_left]
  ring

lemma normalized_profile_actual (W : ℝ→ℂ) (B n : ℕ) (s t x : ℝ) :
    normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n s t x=
      (heightScale B n s t:ℂ)*CenteredMomentReflectedAnnuli.annularProfile
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) s x := by
  unfold normalizedReflected
  rw [actual_log_window]
  unfold CenteredMomentReflectedAnnuli.annularProfile
  ring

theorem actual_annular_normalization (χ : Character) (W : ℝ→ℂ) (B n : ℕ)
    (k : ℤ) (t Y : ℝ) :
    (Real.sqrt (dyadicScale k):ℂ)*HeckeDyadic.polynomial χ false
      (CenteredMomentReflectedAnnuli.annularProfile
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (dyadicScale k))
      (dyadicScale k*Y) 0 0=
      (((1+‖t‖)^n:ℝ):ℂ)*(CenteredMomentReflectedAnnuli.annularMass B k:ℂ)*
        HeckeDyadic.polynomial χ false
          (normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n (dyadicScale k) t)
          (dyadicScale k*Y) 0 0 := by
  have hf : normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n (dyadicScale k) t=
      (fun x=>(heightScale B n (dyadicScale k) t:ℂ)*
        CenteredMomentReflectedAnnuli.annularProfile
          (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (dyadicScale k) x) :=
    funext (normalized_profile_actual W B n (dyadicScale k) t)
  rw [hf,polynomial_const]
  have hh : (1+‖t‖)^n*CenteredMomentReflectedAnnuli.annularMass B k*
      heightScale B n (dyadicScale k) t=Real.sqrt (dyadicScale k) := by
    unfold CenteredMomentReflectedAnnuli.annularMass heightScale
    have ht : (1+‖t‖)^n≠0 := ne_of_gt (by positivity)
    have hs : (1+dyadicScale k)^B≠0 := ne_of_gt (by have := dyadicScale_pos k;positivity)
    field_simp
  have hc : (((1+‖t‖)^n:ℝ):ℂ)*(CenteredMomentReflectedAnnuli.annularMass B k:ℂ)*
      (heightScale B n (dyadicScale k) t:ℂ)=(Real.sqrt (dyadicScale k):ℂ) := by
    rw [←Complex.ofReal_mul,←Complex.ofReal_mul,hh]
  rw [←mul_assoc _ (heightScale B n (dyadicScale k) t:ℂ),hc]

end SevenEighths.CenteredMomentReflectedNormalization

end

end OAI
