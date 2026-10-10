import Mathlib.Analysis.MellinInversion
import OAI.NumberTheory.Jacobsthal.Analysis.RieszIntegralRepresentation
import OAI.NumberTheory.Ostmann.Dirichlet.LogDerivativeRight
import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitMellin

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet
open MeasureTheory Filter
open scoped Topology BigOperators SchwartzMap

variable (ρ : 𝓢(ℝ, ℂ))
local notation "smoothKernel" => mellin (ρ : ℝ → ℂ)

lemma smoothTerm_integral (f : ℕ → ℂ) (hf0 : f 0 = 0) {sigma X : ℝ}
    (hs : 0 < sigma) (hX : 0 < X) (n : ℕ) :
    mellinFactor * (∫ t:ℝ, smoothDirichletTerm ρ f sigma X n t) =
      f n * (ρ ((n:ℝ)/X):ℂ) := by
  by_cases hn : n=0
  · simp [smoothDirichletTerm,hn,hf0]
  · have hr : 0 < (n:ℝ)/X := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hX
    have hi := schwartz_mellin_inversion_integral ρ sigma hs hr
    have hi' : mellinFactor * (∫ t:ℝ, (((n:ℝ)/X:ℝ):ℂ)^(-((sigma:ℂ)+(t:ℂ)*Complex.I)) *
        smoothKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)) = (ρ ((n:ℝ)/X):ℂ) := by
      simpa only [mellinInv,smul_eq_mul,RCLike.real_smul_eq_coe_mul,mellinFactor] using! hi
    have he : (∫ t:ℝ, smoothDirichletTerm ρ f sigma X n t) =
        f n * (∫ t:ℝ, (((n:ℝ)/X:ℝ):ℂ)^(-((sigma:ℂ)+(t:ℂ)*Complex.I)) *
          smoothKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
      simp_rw [smoothDirichletTerm_eq_scaled ρ f hf0 sigma hX n,mul_assoc]
      exact integral_const_mul _ _
    rw [he]
    calc
      _ = f n * (mellinFactor * (∫ t:ℝ, (((n:ℝ)/X:ℝ):ℂ)^(-((sigma:ℂ)+(t:ℂ)*Complex.I)) *
          smoothKernel ((sigma:ℂ)+(t:ℂ)*Complex.I))) := by ring
      _ = _ := by rw [hi']

theorem hasSum_smooth_integral (f : ℕ → ℂ) (hf0 : f 0 = 0) {sigma X : ℝ}
    (hs : 0 < sigma) (hf : LSeriesSummable f (sigma:ℂ)) (hX : 0 < X) :
    HasSum (fun n:ℕ => f n*(ρ ((n:ℝ)/X):ℂ))
      (mellinFactor * ∫ t:ℝ, LSeries f ((sigma:ℂ)+(t:ℂ)*Complex.I) *
        smoothKernel ((sigma:ℂ)+(t:ℂ)*Complex.I) * (X:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
  have hnorm : Summable (fun n:ℕ => ∫ t:ℝ, ‖smoothDirichletTerm ρ f sigma X n t‖) := by
    simp_rw [integral_norm_smoothDirichletTerm ρ f hX]
    exact (hf.norm.mul_right (X^sigma)).mul_right _
  have h := hasSum_integral_of_summable_integral_norm
    (fun n:ℕ => integrable_smoothDirichletTerm ρ f hs hX n) hnorm
  have hscaled := h.mul_left mellinFactor
  simp_rw [smoothTerm_integral ρ f hf0 hs hX] at hscaled
  have hseries (t:ℝ) : (∑' n:ℕ, smoothDirichletTerm ρ f sigma X n t) =
      LSeries f ((sigma:ℂ)+(t:ℂ)*Complex.I) * smoothKernel ((sigma:ℂ)+(t:ℂ)*Complex.I) *
        (X:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I) := by
    simp only [smoothDirichletTerm,tsum_mul_right,LSeries]
  simp_rw [hseries] at hscaled
  exact hscaled

theorem character_smooth_mellin {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma X : ℝ} (hs : 1 < sigma) (hX : 0 < X) :
    (∑' n:ℕ, (chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) * (ρ ((n:ℝ)/X):ℂ)) =
      mellinFactor * ∫ t:ℝ,
        (-deriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I) /
          DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I)) *
        smoothKernel ((sigma:ℂ)+(t:ℂ)*Complex.I) * (X:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I) := by
  have hf0 : (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) 0 = 0 := by simp
  have hf : LSeriesSummable (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) (sigma:ℂ) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi (by simpa using hs)
  rw [(hasSum_smooth_integral ρ _ hf0 (by linarith) hf hX).tsum_eq]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    dsimp only
    rw [twisted_series_eq_actual_log_derivative chi (by simpa using hs)])

end Ostmann.Dirichlet

end OAI
