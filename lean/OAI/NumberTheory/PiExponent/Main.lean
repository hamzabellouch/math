import OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixGeometry
import OAI.NumberTheory.PiExponent.Approximation.InterpolationConsequence

namespace OAI

namespace PiExponent

theorem pi_eventual_lower_bound : PiEventualLowerBound :=
  piEventualLowerBound_of_globalInterpolation AdmissibleMatrixInterpolation.globalInterpolation

theorem pi_integer_eventual_lower_bound : IntegerEventualLowerBound Real.pi :=
  (eventualLowerBound_iff_integer Real.pi).mp pi_eventual_lower_bound

theorem pi_irrationalityExponent_eq_two : irrationalityExponent Real.pi = 2 :=
  pi_irrationalityExponent_eq_two_of_eventualLowerBound pi_eventual_lower_bound

theorem main :
  (∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
    ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-ν) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) ∧
  sSup {ν : ℝ | 0 < ν ∧
    Set.Infinite {r : ℚ | 2 ≤ r.den ∧
      0 < |Real.pi - (r : ℝ)| ∧
      |Real.pi - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}} = 2 := by
  refine ⟨pi_integer_eventual_lower_bound, ?_⟩
  change irrationalityExponent Real.pi = 2
  exact pi_irrationalityExponent_eq_two

theorem flint_hills_summable :
    Summable (fun n : ℕ =>
      1 / (((n + 1 : ℕ) : ℝ) ^ 3 * Real.sin (n + 1 : ℕ) ^ 2)) :=
  flintHills_positive_summable_of_eventual_lower_bound pi_eventual_lower_bound

end PiExponent

end OAI
