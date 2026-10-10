import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterContourZeros
import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedLogDerivative

namespace OAI

/-! # The zeros of the entire completed character L-function -/

namespace Ostmann

open Complex

theorem PrimitiveComplexCharacter.completed_order_ne_top (χ : PrimitiveComplexCharacter)
    (z : ℂ) : analyticOrderAt χ.completed z ≠ ⊤ := by
  intro h
  have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z χ.completed_analytic).mp h
  exact χ.completed_ne_zero_right 2 (by norm_num) (congrFun he 2)

theorem PrimitiveComplexCharacter.completed_zero_iff (χ : PrimitiveComplexCharacter)
    (z : ℂ) : χ.completed z = 0 ↔ z ∈ complexCharacterZeros χ := by
  constructor
  · intro hz
    have hpos : 0 < z.re := by
      by_contra h
      exact χ.completed_ne_zero_left z (not_lt.mp h) hz
    have hlt : z.re < 1 := by
      by_contra h
      exact χ.completed_ne_zero_right z (not_lt.mp h) hz
    refine ⟨hpos, hlt, ?_⟩
    have he := congrFun χ.L_eq_completed_mul_all z
    change χ.L z = χ.completed z * χ.gammaInverse z at he
    rw [he, hz, zero_mul]
  · rintro ⟨hpos, _, hzero⟩
    have he := congrFun χ.L_eq_completed_mul_all z
    change χ.L z = χ.completed z * χ.gammaInverse z at he
    rw [hzero] at he
    exact (mul_eq_zero.mp he.symm).resolve_right (χ.gammaInverse_ne_zero z hpos)

end Ostmann

end OAI
