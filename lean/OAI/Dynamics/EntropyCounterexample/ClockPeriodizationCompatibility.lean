import OAI.Dynamics.EntropyCounterexample.ClockQuotient

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace Problem340.ClockQuotient

variable {E F : Type*}

theorem periodize_eq_clockPeriodization [TopologicalSpace E] [NormedAddCommGroup F]
    {P a b : ℝ} {f : ℝ × E → F} (hP : 0 < P)
    (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    periodize P f = ClockPeriodization.periodize P f := by
  funext x
  exact periodize_eq_tsum hP hsupp x

theorem contDiff_periodize [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P a b : ℝ} {n : ℕ∞ω} {f : ℝ × E → F} (hP : 0 < P)
    (hf : ContDiff ℝ n f) (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    ContDiff ℝ n (periodize P f) := by
  rw [periodize_eq_clockPeriodization hP hsupp]
  exact ClockPeriodization.contDiff_periodize hP hf hsupp

end Problem340.ClockQuotient

end

end OAI
