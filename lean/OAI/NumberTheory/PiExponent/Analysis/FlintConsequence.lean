import OAI.NumberTheory.PiExponent.Analysis.DyadicSpacing
import OAI.NumberTheory.PiExponent.Analysis.FlintSine
import OAI.NumberTheory.PiExponent.Statement

namespace OAI

namespace PiExponent

theorem uniform_pi_distance_of_eventual_lower_bound (h : PiEventualLowerBound)
    {ν : ℝ} (hν : 2 < ν) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - ν) ≤ integerDistance (q * Real.pi) := by
  obtain ⟨Q, hQ, hbound⟩ := h ν hν
  apply uniform_integerDistance_lower_bound irrational_pi
  exact ⟨Q, fun q hq _ p => hbound p q hq⟩

theorem flintHills_summable_of_eventual_lower_bound (h : PiEventualLowerBound) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 3 * Real.sin n ^ 2)) := by
  obtain ⟨c, hc, _, hbound⟩ :=
    uniform_pi_distance_of_eventual_lower_bound h (ν := 9 / 4) (by norm_num)
  exact flintHills_summable_of_distance_summable
    (summable_inverse_cube_integerDistance hc (by norm_num) (by norm_num) hbound)

theorem flintHills_positive_summable_of_eventual_lower_bound (h : PiEventualLowerBound) :
    Summable (fun n : ℕ =>
      1 / (((n + 1 : ℕ) : ℝ) ^ 3 * Real.sin (n + 1 : ℕ) ^ 2)) :=
  (summable_nat_add_iff 1).mpr (flintHills_summable_of_eventual_lower_bound h)

end PiExponent

end OAI
