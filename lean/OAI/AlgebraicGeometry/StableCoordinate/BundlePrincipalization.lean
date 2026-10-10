import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Explicit global principalization in the quadric bundle

This module gives polynomial identities, valid in every commutative ring,
for the principalization in source Section 4, Lemma `bun:principalization`.
Unlike the source proof, the argument uses an explicit global Bezout identity
and requires neither localization nor prime-spectrum gluing.
-/

namespace StableCoordinate.Bundle

variable {R : Type*} [CommRing R]

/-- Pullback of the source element `s_B` under `x = ab`, `y = dc`. -/
def s (a d b c u : R) : R := d * c - (a * b) * (a * b + u ^ 2)

/-- First generator of the pulled-back distinguished ideal. -/
def f₀ (a d b c u : R) : R := a * b - s a d b c u ^ 2 + u ^ 2

/-- Second generator of the pulled-back distinguished ideal. -/
def g₀ (a d b c u : R) : R := d * b - s a d b c u * (a * b)

/-- The global generator of the pulled-back ideal. -/
def v (a d b u : R) : R := a ^ 3 * b + a ^ 2 * u ^ 2 - d ^ 2

/-- First coefficient in the global Bezout relation. -/
def coeffA (a d b : R) : R := a ^ 2 * (1 - 2 * b * d)

/-- Second coefficient in the global Bezout relation. -/
def coeffB (a d b u : R) : R :=
  coeffA a d b * (a * b + u ^ 2) + d ^ 2 * (3 + 2 * b * d)

theorem g₀_factor (a d b c u : R) (h : a * c - b * d = 1) :
    g₀ a d b c u = b ^ 2 * v a d b u := by
  unfold g₀ s v
  linear_combination -(b * d) * h

theorem f₀_factor (a d b c u : R) (h : a * c - b * d = 1) :
    f₀ a d b c u = (c ^ 2 - b ^ 2 * (a * b + u ^ 2)) * v a d b u := by
  unfold f₀ s v
  linear_combination -((a * b + u ^ 2) * (a * c - b * d + 1)) * h

theorem coefficients_bezout (a d b c u : R) (h : a * c - b * d = 1) :
    coeffA a d b * (c ^ 2 - b ^ 2 * (a * b + u ^ 2)) +
      coeffB a d b u * b ^ 2 = 1 := by
  unfold coeffB coeffA
  linear_combination (1 - 2 * b * d) * (a * c + b * d + 1) * h

theorem generator_bezout (a d b c u : R) (h : a * c - b * d = 1) :
    coeffA a d b * f₀ a d b c u + coeffB a d b u * g₀ a d b c u =
      v a d b u := by
  rw [f₀_factor a d b c u h, g₀_factor a d b c u h]
  rw [← mul_assoc, ← mul_assoc, ← add_mul, coefficients_bezout a d b c u h, one_mul]

/-- The exact global principalization claimed in Section 4. -/
theorem principalization (a d b c u : R) (h : a * c - b * d = 1) :
    Ideal.span ({f₀ a d b c u, g₀ a d b c u} : Set R) =
      Ideal.span ({v a d b u} : Set R) := by
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · apply Ideal.mem_span_singleton.2
      exact ⟨c ^ 2 - b ^ 2 * (a * b + u ^ 2), by
        rw [f₀_factor a d b c u h, mul_comm]⟩
    · obtain rfl := Set.mem_singleton_iff.mp hz
      apply Ideal.mem_span_singleton.2
      exact ⟨b ^ 2, by rw [g₀_factor a d b c u h, mul_comm]⟩
  · apply Ideal.span_le.2
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact Ideal.mem_span_pair.2
      ⟨coeffA a d b, coeffB a d b u, generator_bezout a d b c u h⟩

/-- Membership in the pulled-back ideal gives an actual factorization by `v`. -/
theorem exists_factor_of_mem (a d b c u : R) (h : a * c - b * d = 1)
    {r : R} (hr : r ∈ Ideal.span ({f₀ a d b c u, g₀ a d b c u} : Set R)) :
    ∃ q : R, r = v a d b u * q := by
  rw [principalization a d b c u h, Ideal.mem_span_singleton] at hr
  rcases hr with ⟨q, hq⟩
  exact ⟨q, hq⟩

end StableCoordinate.Bundle

end OAI
