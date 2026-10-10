import Mathlib.MeasureTheory.Integral.Pi
import OAI.Combinatorics.BalancedRyser.Probability.ConditionalRestriction

namespace OAI

namespace Balanced.ConditionalRestriction

noncomputable section
open scoped Classical BigOperators
open MeasureTheory TupleAlignment

variable {D A : Type*} [Fintype D] [Fintype A] [DecidableEq D] [Nonempty A]

def fixArray (P : D → Prop) (a ω : D → A) : D → A :=
  fun d => if P d then a d else ω d

theorem uniform_map_fixArray (P : D → Prop) (a : D → A) :
    (PMF.uniformOfFintype (D → A)).map (fixArray P a) =
      (PMF.uniformOfFintype (D → A)).filter
        {ω | ∀ d, P d → ω d = a d} (fixed_supported P a) := by
  let e : {d : D // ¬ P d} ↪ D := ⟨Subtype.val, Subtype.val_injective⟩
  have hr := uniform_map_restrict (A := A) e
  have he := uniform_map_equiv (fixedFreshEquiv P a).symm
  rw [uniform_fixed_filter, ← he, PMF.map_comp, ← hr, PMF.map_comp]
  congr 1

variable [MeasurableSpace A] [MeasurableSingletonClass A]

theorem pi_uniform_toMeasure :
    Measure.pi (fun _ : D => (PMF.uniformOfFintype A).toMeasure) =
      (PMF.uniformOfFintype (D → A)).toMeasure := by
  apply Measure.ext_of_singleton
  intro ω
  rw [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.uniformOfFintype_apply, Nat.cast_pow, ENNReal.inv_pow]

theorem integral_fixArray_eq_filtered (P : D → Prop) (a : D → A) (f : (D → A) → ℝ) :
    (∫ ω, f (fixArray P a ω) ∂Measure.pi
      (fun _ : D => (PMF.uniformOfFintype A).toMeasure)) =
    ∫ ω, f ω ∂((PMF.uniformOfFintype (D → A)).filter
      {ω | ∀ d, P d → ω d = a d} (fixed_supported P a)).toMeasure := by
  rw [pi_uniform_toMeasure, ← uniform_map_fixArray,
    ← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  symm
  exact integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable

end
end Balanced.ConditionalRestriction

end OAI
