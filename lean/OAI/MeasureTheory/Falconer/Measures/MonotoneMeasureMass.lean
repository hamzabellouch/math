import OAI.MeasureTheory.Falconer.Shells.MonotoneShellVariation
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

namespace OAI

/-!
# Positive increments of decreasing finite measures

This is the measure-theoretic telescoping step of `asm:monotone-shell`.
The total variation of each positive decrement is its mass, and those
masses are summable. No quantitative convergence rate is introduced.
-/

namespace Falconer
open MeasureTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- The finite telescoping identity is an equality of measures, not just of
masses. Each difference is the positive measure difference. -/
theorem antitone_measure_sum_decrements (α : ℕ → Measure X)
    [∀ n, IsFiniteMeasure (α n)] (hα : Antitone α) (N : ℕ) :
    (∑ n ∈ Finset.range N, (α n - α (n + 1))) + α N = α 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_assoc,
      Measure.sub_add_cancel_of_le (hα (Nat.le_succ N))]
    exact ih

/-- Monotonicity and finite initial mass supply precisely the summability
needed for the variation correction in the shell argument. -/
theorem summable_antitone_measure_decrements (α : ℕ → Measure X)
    [∀ n, IsFiniteMeasure (α n)] (hα : Antitone α) :
    Summable (fun n => (α n - α (n + 1)).real univ) := by
  have hm : Antitone (fun n => (α n).real univ) := by
    intro i j hij
    exact ENNReal.toReal_mono (measure_ne_top (α i) univ) (hα hij univ)
  have hsum := summable_antitone_mass_increments (fun n => (α n).real univ)
    hm (fun _ => measureReal_nonneg)
  convert hsum using 1
  funext n
  rw [Measure.real, Measure.sub_apply MeasurableSet.univ (hα (Nat.le_succ n)),
    ENNReal.toReal_sub_of_le (hα (Nat.le_succ n) univ) (measure_ne_top (α n) univ)]
  rfl

end Falconer

end OAI
