import OAI.NumberTheory.Ostmann.ZeroDensity.GammaGrowthStrip
import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedLogDerivative

namespace OAI

/-! # Uniform Gamma factors for the horizontal-contour growth estimate -/

namespace Ostmann

open Complex
open scoped Classical

theorem characterGamma_growth_bounds : ∃ C : ℝ, 0 < C ∧
    (∀ (χ : PrimitiveComplexCharacter) (s : ℂ), (1 / 2 : ℝ) ≤ s.re → s.re ≤ 7 / 4 →
      ‖DirichletCharacter.gammaFactor χ.character s‖ ≤ C) ∧
    (∀ (χ : PrimitiveComplexCharacter) (s : ℂ), -(3 / 4 : ℝ) ≤ s.re → s.re ≤ 1 / 2 →
      ‖χ.gammaInverse s‖ ≤ C * Real.exp (Real.pi * |s.im|)) := by
  obtain ⟨C, hC, hp, hi⟩ := gammaReal_growth_bounds
  refine ⟨C, hC, ?_, ?_⟩
  · intro χ s hs hs'
    by_cases hc : χ.character.Even
    · simpa only [DirichletCharacter.gammaFactor, hc, ↓reduceIte] using hp s hs (by linarith)
    · simpa only [DirichletCharacter.gammaFactor, hc, ↓reduceIte] using
        hp (s + 1) (by simp; linarith) (by simp; linarith)
  · intro χ s hs hs'
    by_cases hc : χ.character.Even
    · simpa only [PrimitiveComplexCharacter.gammaInverse, DirichletCharacter.gammaFactor, hc, ↓reduceIte]
        using hi s hs (by linarith)
    · simpa only [PrimitiveComplexCharacter.gammaInverse, DirichletCharacter.gammaFactor, hc, ↓reduceIte,
        add_im, one_im, add_zero] using hi (s + 1) (by simp; linarith) (by simp; linarith)

theorem PrimitiveComplexCharacter.L_reflection_product (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : s.re < 1) :
    χ.L s = (χ.modulus : ℂ) ^ (1 / 2 - s) *
      @DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character *
      χ.inverse.L (1 - s) * DirichletCharacter.gammaFactor χ.inverse.character (1 - s) *
      χ.gammaInverse s := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hpos : 0 < (1 - s).re := by simp; linarith
  have hgne : DirichletCharacter.gammaFactor χ.inverse.character (1 - s) ≠ 0 := by
    intro hz
    have hh := χ.inverse.gammaInverse_ne_zero _ hpos
    apply hh
    change (DirichletCharacter.gammaFactor χ.inverse.character (1 - s))⁻¹ = 0
    rw [hz, inv_zero]
  have hLi := congrFun χ.inverse.L_eq_completed_mul_all (1 - s)
  change χ.inverse.L (1 - s) = χ.inverse.completed (1 - s) /
    DirichletCharacter.gammaFactor χ.inverse.character (1 - s) at hLi
  have hCi := (eq_div_iff hgne).mp hLi
  have hfun := χ.primitive.completedLFunction_one_sub (1 - s)
  have harg : 1 - (1 - s) = s := by ring
  have hexp : (1 - s) - 1 / 2 = 1 / 2 - s := by ring
  rw [harg, hexp] at hfun
  have hL := congrFun χ.L_eq_completed_mul_all s
  change χ.L s = χ.completed s * χ.gammaInverse s at hL
  rw [hL]
  change χ.completed s = (χ.modulus : ℂ) ^ (1 / 2 - s) *
    DirichletCharacter.rootNumber χ.character * χ.inverse.completed (1 - s) at hfun
  rw [hfun, ← hCi]
  ring

end Ostmann

end OAI
