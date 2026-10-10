import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Exact arithmetic reindexing in the divisor graph

The change of variables turns two divisor representations into an additive
edge. The underlying integer identities hold in both directions without
asymptotic hypotheses.
-/

namespace JointDickman

/-- Reconstruct the second quotient and the additive edge from the first
quotient. All variables are integers, allowing both signs of the lag. -/
theorem divisor_edge_forward {a b c j m z : ℤ}
    (hcoeff : a - b = j * c) (hquot : c * z = a * m + 1) :
    c * (z - j * m) = b * m + 1 ∧
      b * z + j = a * (z - j * m) := by
  constructor
  · linear_combination hquot + m * hcoeff
  · linear_combination -z * hcoeff - j * hquot

/-- The congruence at the new endpoint reconstructs the old divisor
representation. Coprimality with the lag is precisely the cancellation
needed in the reverse direction. -/
theorem divisor_edge_iff {a b c j z : ℤ}
    (hcoeff : a - b = j * c) (hcop : IsCoprime a j) :
    (∃ m : ℤ, c * z = a * m + 1) ↔ a ∣ b * z + j := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨z - j * m, (divisor_edge_forward hcoeff hm).2⟩
  · rintro ⟨k, hk⟩
    have hdiv : a ∣ j * (c * z - 1) := by
      refine ⟨z - k, ?_⟩
      linear_combination -z * hcoeff - hk
    obtain ⟨m, hm⟩ := hcop.dvd_of_dvd_mul_left hdiv
    exact ⟨m, by linarith⟩

/-- No multiplicity is introduced by the reindexing. -/
theorem divisor_edge_quotient_unique {a c z m₁ m₂ : ℤ} (ha : a ≠ 0)
    (hm₁ : c * z = a * m₁ + 1) (hm₂ : c * z = a * m₂ + 1) : m₁ = m₂ := by
  apply mul_left_cancel₀ ha
  linarith

/-- Both old divisibility conditions imply the coefficient difference is
divisible by `c`, because the multiplier is a unit modulo `c`. -/
theorem common_divisor_difference {a b c m : ℤ}
    (ha : c ∣ a * m + 1) (hb : c ∣ b * m + 1) : c ∣ a - b := by
  have hm : IsCoprime c m := by
    obtain ⟨z, hz⟩ := ha
    refine ⟨z, -a, ?_⟩
    linear_combination -hz
  apply hm.dvd_of_dvd_mul_right
  convert dvd_sub ha hb using 1
  ring

end JointDickman

end OAI
