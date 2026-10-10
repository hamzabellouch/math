import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterHadamardBounds
import OAI.NumberTheory.Ostmann.ZeroDensity.ImprimitiveEulerBound

namespace OAI

/-! # The logarithmic-derivative lower bound at an arbitrary character level -/

namespace Ostmann

open Complex

noncomputable def primitiveOfNonprincipal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : PrimitiveComplexCharacter where
  modulus := χ.conductor
  positive := Nat.pos_of_ne_zero χ.conductor_ne_zero
  character := χ.primitiveCharacter
  primitive := χ.primitiveCharacter_isPrimitive
  nontrivial := by
    intro he
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, he, DirichletCharacter.changeLevel_one]

theorem primitiveOfNonprincipal_logDeriv_difference {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunction χ) s -
      logDeriv (primitiveOfNonprincipal χ hχ).L s‖ ≤ Real.log q := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hh := logDeriv_changeLevel_bound χ.primitiveCharacter χ.conductor_dvd_level s hs
  rw [χ.changeLevel_primitiveCharacter] at hh
  exact hh

/-- Only a logarithmic modulus loss is incurred by imprimitive characters. -/
theorem exists_nonprincipal_logDeriv_real_lower : ∃ B : ℝ, 0 < B ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
        -(3 / 2) * Real.log q - B * Real.log (|s.im| + 2) ≤
          (logDeriv (DirichletCharacter.LFunction χ) s).re := by
  obtain ⟨B, hB, hb⟩ := exists_character_logDeriv_real_lower
  refine ⟨B, hB, ?_⟩
  intro q _ χ hχ s hs hs2
  have hprimitive := hb (primitiveOfNonprincipal χ hχ) s hs hs2
  have herr := primitiveOfNonprincipal_logDeriv_difference χ hχ s hs
  have hre := Complex.re_le_norm (-(logDeriv (DirichletCharacter.LFunction χ) s -
    logDeriv (primitiveOfNonprincipal χ hχ).L s))
  rw [Complex.neg_re, Complex.sub_re, norm_neg] at hre
  have hlog : Real.log χ.conductor ≤ Real.log q :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero)
      (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level)
  change -(1 / 2) * Real.log χ.conductor - B * Real.log (|s.im| + 2) ≤ _ at hprimitive
  linarith

end Ostmann

end OAI
