import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace GrahamSpherical

/-- Only the algebraic quotient rule is used; no continuity or differentiation
of the infinite series defining the parameter is involved. -/
theorem derivation_rotation_coordinates (D : Derivation ℤ ℝ ℝ) (t : ℝ)
    (ht : D t = (1 + t ^ 2) / 2) :
    D ((1 - t ^ 2) / (1 + t ^ 2)) = -(2 * t / (1 + t ^ 2)) ∧
      D (2 * t / (1 + t ^ 2)) = (1 - t ^ 2) / (1 + t ^ 2) := by
  have hden : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  have htwo : D (2 : ℝ) = 0 := D.map_natCast 2
  have hpow : D (t ^ 2) = 2 * t * D t := by
    simp [Derivation.leibniz_pow, smul_eq_mul, two_smul]
    ring
  constructor
  · rw [D.leibniz_div, map_sub, map_add, D.map_one_eq_zero, hpow, ht]
    simp only [smul_eq_mul]
    field_simp [hden]
    ring
  · rw [D.leibniz_div, D.leibniz, map_add, D.map_one_eq_zero, htwo, hpow, ht]
    simp only [smul_eq_mul]
    field_simp [hden]
    ring

end GrahamSpherical

end OAI
