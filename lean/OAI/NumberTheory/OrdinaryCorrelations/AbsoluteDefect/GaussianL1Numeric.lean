import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicLogWindowSmall
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BumpMass
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicCoefficientSum

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

namespace OrdinaryChainScales
open OrdinaryCorrelations SourcePrimeFactor OrdinaryDirichletMeanSquare OrdinaryGaussianWindow
open Finset Filter MeasureTheory

lemma gaussian_l1_numeric {ε w E I M : ℝ} (hε : 0<ε) (hw : 0<w)
    (hE : E<ε^2/12*w^2) (htail : w*M<ε/4)
    (hI : I≤3*(ε*w/12)+E/(4*(ε*w/12))+w^2*M) : I<ε*w := by
  have hdiv : E/(4*(ε*w/12))<ε*w/4 := by
    apply (div_lt_iff₀ (by positivity : 0<4*(ε*w/12))).2
    nlinarith only [hE]
  have htail' := mul_lt_mul_of_pos_right htail hw
  nlinarith only [hI,hdiv,htail',mul_pos hε hw]

theorem dyadic_gaussian_l1_small {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {d : ℕ} (hd : 0<d) (χ : DirichletCharacter ℂ d) {ε : ℝ} (hε : 0<ε) :
    ∃D0 : ℕ,0<D0 ∧ ∀D : ℝ,(D0:ℝ)≤D → ∀ᶠ X : ℕ in atTop,
      (∫x : ℝ,‖scaledWindow (Ioc X (2*X))
        (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n) (D/(X:ℝ)) x‖)
      < ε*(D/(X:ℝ)) := by
  obtain ⟨D0,hD0,hE⟩ := dyadic_log_window_small hf hm hNP hd χ
    (by positivity : 0<ε^2/12)
  refine ⟨D0,hD0,?_⟩
  intro D hD
  have hDp : 0<D := (by exact_mod_cast hD0 : (0:ℝ)<D0).trans_le hD
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
  exact gaussian_l1_numeric hε hwidth (hEX D hD) htail hbound'

end OrdinaryChainScales

end

end OAI
