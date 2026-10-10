import OAI.NumberTheory.CubicMoment.Estimates.PrimeExclusion
import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicPrimeSaving

namespace OAI

/-! The numerator-independent coprimality exclusion in the actual smooth
prime sum, with the error supplied by the proved divisor bound. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def excludedSmoothPrimeCharacterSum (R Y : ℝ) (w : ℝ → ℂ)
    (χ : Eisenstein → ℂ) (e : Eisenstein) (u : ℝ) : ℂ :=
  ∑ p ∈ primeCutoff (R*Y) with IsCoprime p e,
    w (norm p/Y)*mellinPhase u (norm p)*χ p

theorem excluded_prime_input_error {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R Y M : ℝ) (w : ℝ → ℂ) (χ : Eisenstein → ℂ),
      0 ≤ M → (∀ x, ‖w x‖ ≤ M) → (∀ p ∈ primeCutoff (R*Y), ‖χ p‖ ≤ 1) →
      ∀ e : Eisenstein, e ≠ 0 → ∀ u : ℝ,
      ‖excludedSmoothPrimeCharacterSum R Y w χ e u-smoothPrimeCharacterSum R Y w χ u‖ ≤
        C*norm e^ε*M := by
  obtain ⟨C,hC,hbound⟩ := prime_exclusion_small_power hε
  refine ⟨C,hC,?_⟩
  intro R Y M w χ hM hw hχ e he u
  rw [norm_sub_rev]
  apply hbound (primeCutoff (R*Y)) (fun p hp => (mem_primeCutoff.mp hp).1) e he
    (fun p => w (norm p/Y)*mellinPhase u (norm p)*χ p) M hM
  intro p hp
  rw [norm_mul,norm_mul,mellinPhase_norm,mul_one]
  exact (mul_le_of_le_one_right (_root_.norm_nonneg _) (hχ p hp)).trans (hw _)

theorem excluded_smooth_prime_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R Y M E : ℝ) (w : ℝ → ℂ) (χ : Eisenstein → ℂ),
      0 ≤ M → (∀ x, ‖w x‖ ≤ M) → (∀ p ∈ primeCutoff (R*Y), ‖χ p‖ ≤ 1) →
      ∀ e : Eisenstein, e ≠ 0 → ∀ u : ℝ, ‖smoothPrimeCharacterSum R Y w χ u‖ ≤ E →
      ‖excludedSmoothPrimeCharacterSum R Y w χ e u‖ ≤ E+C*norm e^ε*M := by
  obtain ⟨C,hC,hbound⟩ := excluded_prime_input_error hε
  refine ⟨C,hC,?_⟩
  intro R Y M E w χ hM hw hχ e he u hE
  calc
    _ = ‖smoothPrimeCharacterSum R Y w χ u+
        (excludedSmoothPrimeCharacterSum R Y w χ e u-smoothPrimeCharacterSum R Y w χ u)‖ := by
      congr 1
      ring
    _ ≤ ‖smoothPrimeCharacterSum R Y w χ u‖+
        ‖excludedSmoothPrimeCharacterSum R Y w χ e u-smoothPrimeCharacterSum R Y w χ u‖ :=
      norm_add_le _ _
    _ ≤ _ := add_le_add hE (hbound R Y M w χ hM hw hχ e he u)

end CubicFirstMoment

end

end OAI
