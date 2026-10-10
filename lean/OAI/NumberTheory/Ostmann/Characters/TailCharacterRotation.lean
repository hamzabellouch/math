import OAI.NumberTheory.Ostmann.Construction.TypicalCharacterEndpoints

namespace OAI

/-! # A common rotation for the actual translated character averages -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def translatedTailCharacterMean (A : Set ℕ) (N : ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (center : ∀ p : ℕ, ZMod p) (p : ℕ) : ℂ :=
  (∑ r ∈ tailSupport A N p, χ p ((r : ZMod p) - center p)) /
    ((tailSupport A N p).card : ℂ)

theorem realTranslatedCharacterTest_mean (A : Set ℕ) (N : ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (center : ∀ p : ℕ, ZMod p) (ζ : ℂ) (p : ℕ) :
    residueTestMean (tailSupport A N p) (realTranslatedCharacterTest χ center ζ p) =
      (ζ * translatedTailCharacterMean A N χ center p).re := by
  unfold residueTestMean realTranslatedCharacterTest translatedTailCharacterMean
  rw [← mul_div_assoc]
  simp_rw [Finset.mul_sum]
  rw [show ((tailSupport A N p).card : ℂ) = (((tailSupport A N p).card : ℝ) : ℂ) by simp,
    Complex.div_ofReal_re]
  simp only [Complex.re_sum]

theorem common_positive_tail_character_rotation (A : Set ℕ) (N : ℕ) (P : Finset ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (center : ∀ p : ℕ, ZMod p) (δ : ℝ)
    (hm : ∀ p ∈ P, δ ≤ ‖translatedTailCharacterMean A N χ center p‖) :
    ∃ ζ : ℂ, ∃ E : Finset ℕ, ‖ζ‖ = 1 ∧ E ⊆ P ∧
      (∑ p ∈ P, (p : ℝ)⁻¹) / 4 ≤ ∑ p ∈ E, (p : ℝ)⁻¹ ∧
      ∀ p ∈ E, δ / 2 ≤ residueTestMean (tailSupport A N p)
        (realTranslatedCharacterTest χ center ζ p) := by
  obtain ⟨ζ, E, hζ, hEP, hmass, hmean⟩ := common_positive_character_rotation P
    (translatedTailCharacterMean A N χ center) δ hm
  exact ⟨ζ, E, hζ, hEP, hmass, fun p hp => by
    rw [realTranslatedCharacterTest_mean]
    exact hmean p hp⟩

end Ostmann

end OAI
