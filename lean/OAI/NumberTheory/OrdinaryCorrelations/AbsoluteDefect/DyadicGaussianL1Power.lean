import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicLogWindowPowerLogarithmic
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.GaussianL1Numeric

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
open MeasureTheory Finset

namespace OrdinaryMellinModulus
open OrdinaryCorrelations SourcePrimeFactor OrdinaryDirichletMeanSquare OrdinaryGaussianWindow
open OrdinaryChainScales Finset Filter MeasureTheory

theorem dyadic_gaussian_l1_power_logarithmic :
    ∃ A c : ℕ, ∀ m : ℕ,
    ∀ {f : ℕ→ℂ}, OneBounded f → Multiplicative f → UniformlyNonpretentious f →
    ∀ {d : ℕ}, 0<d → ∀χ : DirichletCharacter ℂ d,
      ∀D : ℝ,
      ((16*(2*m+2+c+1)*2^(2^(29*(2*m+2+3)+A)):ℕ):ℝ)≤D →
      ∀ᶠ X : ℕ in atTop,
      (∫x : ℝ,‖scaledWindow (Ioc X (2*X))
        (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n) (D/(X:ℝ)) x‖)
      < (1/2:ℝ)^m*(D/(X:ℝ)) := by
  obtain ⟨A,c,hA⟩ := dyadic_log_window_power_logarithmic
  refine ⟨A,c,?_⟩
  intro m f hf hm hNP d hd χ
  let ε : ℝ := (1/2:ℝ)^m
  have hε : 0<ε := by dsimp [ε]; positivity
  have hE := hA (2*m+2) hf hm hNP hd χ
  intro D hD
  have hD0 : (0:ℕ)<16*(2*m+2+c+1)*2^(2^(29*(2*m+2+3)+A)) := by positivity
  have hDp : 0<D := (by exact_mod_cast hD0 : (0:ℝ)<(16*(2*m+2+c+1)*2^(2^(29*(2*m+2+3)+A)):ℕ)).trans_le hD
  obtain ⟨X0,hX0⟩ := exists_nat_gt (4*D*(bumpMoment+1)/ε)
  filter_upwards [hE,eventually_ge_atTop X0,eventually_ge_atTop (1:ℕ)] with X hEX hX0X hXp
  have hXr : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hx : 4*D*(bumpMoment+1)/ε<(X:ℝ) :=
    hX0.trans_le (by exact_mod_cast hX0X)
  have hwidth : 0<D/(X:ℝ) := div_pos hDp hXr
  have htail : (D/(X:ℝ))*bumpMoment<ε/4 := by
    have hh := (div_lt_iff₀ hε).mp hx
    apply (lt_div_iff₀ (by norm_num : (0:ℝ)<4)).2
    have he : D/(X:ℝ)*bumpMoment*4=(4*D*bumpMoment)/(X:ℝ) := by ring
    rw [he]
    apply (div_lt_iff₀ hXr).2
    nlinarith only [hh,hDp]
  have hbound := scaledWindow_l1_concentration (Ioc X (2*X))
    (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n)
    (dyadic_log_centres (show 0<X by omega))
    (by positivity : 0<ε*(D/(X:ℝ))/12) hwidth
  have hcoeff := mul_le_mul_of_nonneg_right
    (dyadic_coefficient_sum hf χ (show 0<X by omega))
    (mul_nonneg (sq_nonneg (D/(X:ℝ))) bumpMoment_nonneg)
  have hbound' : (∫x : ℝ,‖scaledWindow (Ioc X (2*X))
        (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n) (D/(X:ℝ)) x‖)≤
      3*(ε*(D/(X:ℝ))/12)+
      (∫x : ℝ,‖scaledWindow (Ioc X (2*X))
        (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n) (D/(X:ℝ)) x‖^2)/
        (4*(ε*(D/(X:ℝ))/12))+(D/(X:ℝ))^2*bumpMoment := by
    linarith only [hbound,hcoeff]
  have hEsmall : (1/2:ℝ)^(2*m+2)/4≤ε^2/12 := by
    dsimp [ε]
    rw [pow_add, Nat.mul_comm 2 m, pow_mul]
    norm_num
    nlinarith only [sq_nonneg ((1/2:ℝ)^m)]
  exact gaussian_l1_numeric hε hwidth
    ((hEX D hD).trans_le (mul_le_mul_of_nonneg_right hEsmall (sq_nonneg _))) htail hbound' 

end OrdinaryMellinModulus

end

end OAI
