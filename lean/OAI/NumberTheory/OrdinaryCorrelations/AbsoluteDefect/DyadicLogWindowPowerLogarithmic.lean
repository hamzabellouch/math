import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicGaussianPowerLogarithmic
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ScaledWindow

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction

namespace OrdinaryMellinModulus
open OrdinaryCorrelations SourcePrimeFactor OrdinaryDirichletMeanSquare OrdinaryGaussianWindow
open Finset Filter MeasureTheory

theorem dyadic_log_window_power_logarithmic :
    ∃ A c : ℕ, ∀ m : ℕ,
    ∀ {f : ℕ→ℂ}, OneBounded f → Multiplicative f → UniformlyNonpretentious f →
    ∀ {d : ℕ}, 0<d → ∀χ : DirichletCharacter ℂ d,
      ∀ᶠ X : ℕ in atTop,∀D : ℝ,
      ((16*(m+c+1)*2^(2^(29*(m+3)+A)):ℕ):ℝ)≤D →
      (∫x : ℝ,‖scaledWindow (Ioc X (2*X))
        (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n) (D/(X:ℝ)) x‖^2)
      < (1/2:ℝ)^m/4*(D/(X:ℝ))^2 := by
  obtain ⟨A,c,hA⟩ := dyadic_gaussian_power_logarithmic
  refine ⟨A,c,?_⟩
  intro m f hf hm hNP d hd χ
  filter_upwards [hA m hf hm hNP hd χ,eventually_ge_atTop (1:ℕ)] with X hX hXp
  intro D hD
  have hXr : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hD0 : (0:ℕ)<16*(m+c+1)*2^(2^(29*(m+3)+A)) := by positivity
  have hDp : 0<D := (by exact_mod_cast hD0 : (0:ℝ)<(16*(m+c+1)*2^(2^(29*(m+3)+A)):ℕ)).trans_le hD
  have hwidth : 0<D/(X:ℝ) := div_pos hDp hXr
  rw [scaled_window_spectral_identity _ _ _ hwidth]
  have he (t : ℝ) : (D/(X:ℝ))*t/2=D*t/(2*(X:ℝ)) := by ring
  simp_rw [he]
  have hh := mul_lt_mul_of_pos_left (hX D hD).2 (show 0<(D/(X:ℝ))^2/4 by positivity)
  change (D/(X:ℝ))^2/4*(∫t : ℝ,gaussian (D*t/(2*(X:ℝ)))*‖dyadicCharacterPolynomial f χ X t‖^2)<_
  nlinarith only [hh]

end OrdinaryMellinModulus

end

end OAI
