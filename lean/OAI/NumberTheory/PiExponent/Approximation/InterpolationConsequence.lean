import OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate
import OAI.NumberTheory.PiExponent.Analysis.FlintConsequence
import OAI.NumberTheory.PiExponent.Approximation.Exponent

namespace OAI

namespace PiExponent

theorem piEventualLowerBound_of_globalInterpolation
    (hgeometry : DeterminantContradiction.GlobalInterpolationStatement) :
    PiEventualLowerBound :=
  DeterminantContradiction.piEventualLowerBound_of_interpolation_and_analytic_aggregate
    hgeometry LiteralAnalytic.analyticAggregate

theorem pi_irrationalityExponent_of_globalInterpolation
    (hgeometry : DeterminantContradiction.GlobalInterpolationStatement) :
    irrationalityExponent Real.pi = 2 :=
  pi_irrationalityExponent_eq_two_of_eventualLowerBound
    (piEventualLowerBound_of_globalInterpolation hgeometry)

theorem flintHills_of_globalInterpolation
    (hgeometry : DeterminantContradiction.GlobalInterpolationStatement) :
    Summable (fun n : ℕ =>
      1 / (((n + 1 : ℕ) : ℝ) ^ 3 * Real.sin (n + 1 : ℕ) ^ 2)) :=
  flintHills_positive_summable_of_eventual_lower_bound
    (piEventualLowerBound_of_globalInterpolation hgeometry)

end PiExponent

end OAI
