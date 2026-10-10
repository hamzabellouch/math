import OAI.NumberTheory.CubicMoment.Estimates.WideCoprimeMellin
import OAI.NumberTheory.CubicMoment.Estimates.WideGramDecay

namespace OAI

/-! The proved coprime operator majorant on the full compact norm range.
This keeps the actual quotient rows instead of assuming a thin dyad. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem wideCoprimeRadialForm_norm_le (M : ℝ) (hM : 0 < M) (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1)
    (x y : Eisenstein → ℝ)
    (hx : ∀ h ∈ H, 0 < x h)
    (hy : ∀ a ∈ S, 0 < y a)
    (hlog : ∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S, |Real.log (x h)-Real.log (y a*y b)| ≤ M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖coprimeRadialForm S H v w phase x y W ρ‖ ≤
      (∫ t : ℝ, ‖wideGramMellinCoefficient M hM W hW hW' ρ t‖) *
        coprimeNormMajorant S H U v w := by
  have hc := wideGramMellinCoefficient_integrable M hM W hW hW' ρ
  have hi := hc.mul_bdd
    (coprimeMellinKernel_continuous S H v w phase x y).aestronglyMeasurable
    (Eventually.of_forall
      (norm_coprimeMellinKernel_le S H U hS hU hSU v w phase hphase x y))
  rw [wideCoprimeRadialForm_mellin M hM S H v w phase x y hx hy hlog W hW hW' hρ]
  calc
    _ ≤ ∫ t : ℝ, ‖wideGramMellinCoefficient M hM W hW hW' ρ t *
        coprimeMellinKernel S H v w phase x y t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖wideGramMellinCoefficient M hM W hW hW' ρ t‖ *
        coprimeNormMajorant S H U v w := by
      apply integral_mono hi.norm (hc.norm.mul_const _)
      intro t
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_coprimeMellinKernel_le S H U hS hU hSU v w phase hphase x y t)
        (_root_.norm_nonneg _)
    _ = _ := integral_mul_const _ _

theorem wideCoprimeRadialForm_rapidDecay (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H U : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      (∀ p ∈ U, primaryPrime p) →
      (∀ a ∈ S, primaryPrimeFactors a ⊆ U) →
      ∀ (v w phase : Eisenstein → ℂ), (∀ h ∈ H, ‖phase h‖ ≤ 1) →
      ∀ (x y : Eisenstein → ℝ),
      (∀ h ∈ H, 0 < x h) →
      (∀ a ∈ S, 0 < y a) →
      (∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S, |Real.log (x h)-Real.log (y a*y b)| ≤ M) →
      ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^A * ‖coprimeRadialForm S H v w phase x y W ρ‖ ≤
        C * coprimeNormMajorant S H U v w := by
  obtain ⟨C, hC, hc⟩ := wideGramMellinCoefficient_mass_rapidDecay M hM W hW hW' A
  refine ⟨C, hC, ?_⟩
  intro S H U hS hU hSU v w phase hphase x y hx hy hlog ρ hρ
  calc
    _ ≤ (1+ρ)^A * ((∫ t : ℝ, ‖wideGramMellinCoefficient M hM W hW hW' ρ t‖) *
        coprimeNormMajorant S H U v w) :=
      mul_le_mul_of_nonneg_left
        (wideCoprimeRadialForm_norm_le M hM S H U hS hU hSU v w phase hphase x y hx hy hlog W hW hW' hρ)
        (by positivity)
    _ = ((1+ρ)^A * (∫ t : ℝ, ‖wideGramMellinCoefficient M hM W hW hW' ρ t‖)) *
        coprimeNormMajorant S H U v w := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hc ρ hρ) (coprimeNormMajorant_nonneg _ _ _ _ _)


end CubicFirstMoment

end

end OAI
