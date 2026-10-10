import OAI.NumberTheory.Ostmann.ZeroDensity.GammaRealContourBound
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterContourZeros

namespace OAI

/-! # The actual character Gamma factors on both vertical contour lines -/

namespace Ostmann

open Complex
open scoped Classical

private theorem contourLine_expanded (s : ℂ) (hs : s.re = -(1 / 2 : ℝ) ∨ s.re = 3 / 2) :
    s.re = -(1 / 2 : ℝ) ∨ s.re = 1 / 2 ∨ s.re = 3 / 2 ∨ s.re = 5 / 2 := by
  rcases hs with h | h
  · exact .inl h
  · exact .inr (.inr (.inl h))

private theorem contourLine_shift (s : ℂ) (hs : s.re = -(1 / 2 : ℝ) ∨ s.re = 3 / 2) :
    (s + 1).re = -(1 / 2 : ℝ) ∨ (s + 1).re = 1 / 2 ∨
      (s + 1).re = 3 / 2 ∨ (s + 1).re = 5 / 2 := by
  simp only [add_re, one_re]
  rcases hs with h | h
  · right; left; linarith
  · right; right; right; linarith

theorem PrimitiveComplexCharacter.gammaFactor_differentiableAt
    (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = -(1 / 2 : ℝ) ∨ s.re = 3 / 2) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ.character) s := by
  by_cases hc : χ.character.Even
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, hc])]
    exact gammaReal_differentiableAt s (gammaReal_contour_regular s (contourLine_expanded s hs))
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ ∘ (fun u : ℂ => u + 1) from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, hc])]
    exact (gammaReal_differentiableAt (s + 1) (gammaReal_contour_regular _ (contourLine_shift s hs))).comp s
      (differentiableAt_id.add_const (1 : ℂ))

theorem characterGamma_contour_bound : ∃ B : ℝ, 0 < B ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ),
      (s.re = -(1 / 2 : ℝ) ∨ s.re = 3 / 2) →
      ‖logDeriv (DirichletCharacter.gammaFactor χ.character) s‖ ≤ B * (1 + |s.im|) := by
  obtain ⟨B, hB, hbound⟩ := gammaReal_contour_logDeriv_bound
  refine ⟨B, hB, ?_⟩
  intro χ s hs
  by_cases hc : χ.character.Even
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, hc])]
    exact hbound s (contourLine_expanded s hs)
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ ∘ (fun u : ℂ => u + 1) from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, hc])]
    rw [logDeriv_comp (g := fun u : ℂ => u + 1) (x := s)
      (gammaReal_differentiableAt (s + 1) (gammaReal_contour_regular _ (contourLine_shift s hs)))
      (differentiableAt_id.add_const (1 : ℂ))]
    simpa using hbound (s + 1) (contourLine_shift s hs)

theorem characterGammaInverse_contour_bound : ∃ B : ℝ, 0 < B ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ),
      (s.re = -(1 / 2 : ℝ) ∨ s.re = 3 / 2) →
      ‖logDeriv χ.gammaInverse s‖ ≤ B * (1 + |s.im|) := by
  obtain ⟨B, hB, hbound⟩ := characterGamma_contour_bound
  refine ⟨B, hB, ?_⟩
  intro χ s hs
  have he := logDeriv_fun_zpow (χ.gammaFactor_differentiableAt s hs) (-1 : ℤ)
  have hi : logDeriv χ.gammaInverse s = -logDeriv (DirichletCharacter.gammaFactor χ.character) s := by
    rw [show χ.gammaInverse = (fun x => (DirichletCharacter.gammaFactor χ.character x)⁻¹) from rfl]
    simpa only [zpow_neg_one, Int.cast_neg, Int.cast_one, neg_one_mul] using he
  rw [hi, norm_neg]
  exact hbound χ s hs

end Ostmann

end OAI
