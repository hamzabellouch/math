import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicGaussianSmall
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

namespace OrdinaryChainScales
open OrdinaryCorrelations SourcePrimeFactor OrdinaryDirichletMeanSquare OrdinaryGaussianWindow
open Finset Filter MeasureTheory

theorem dyadic_log_window_small {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {d : ℕ} (hd : 0<d) (χ : DirichletCharacter ℂ d) {ε : ℝ} (hε : 0<ε) :
    ∃D0 : ℕ,0<D0 ∧ ∀ᶠ X : ℕ in atTop,∀D : ℝ,(D0:ℝ)≤D →
      (∫x : ℝ,‖scaledWindow (Ioc X (2*X))
        (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n) (D/(X:ℝ)) x‖^2)
      < ε*(D/(X:ℝ))^2 := by
  obtain ⟨D0,hD0,hg⟩ := dyadic_gaussian_small hf hm hNP hd χ (by positivity : 0<4*ε)
  refine ⟨D0,hD0,?_⟩
  filter_upwards [hg,eventually_ge_atTop (1:ℕ)] with X hX hXp
  intro D hD
  have hXr : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hDp : 0<D := (by exact_mod_cast hD0 : (0:ℝ)<D0).trans_le hD
  have hwidth : 0<D/(X:ℝ) := div_pos hDp hXr
  rw [scaled_window_spectral_identity _ _ _ hwidth]
  have he (t : ℝ) : (D/(X:ℝ))*t/2=D*t/(2*(X:ℝ)) := by ring
  simp_rw [he]
  have hh := mul_lt_mul_of_pos_left (hX D hD).2 (show 0<(D/(X:ℝ))^2/4 by positivity)
  change (D/(X:ℝ))^2/4*(∫t : ℝ,gaussian (D*t/(2*(X:ℝ)))*‖dyadicCharacterPolynomial f χ X t‖^2)<_
  nlinarith only [hh]

end OrdinaryChainScales

end

end OAI
