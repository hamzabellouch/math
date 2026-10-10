import OAI.Analysis.CoulombTransport.Splitting
import OAI.Analysis.CoulombTransport.SplitMeasure

namespace OAI

universe uAlpha uIndex

/-!
# The disjoint-component selection obstruction

This combines the abstract mass argument with the exact mass identities for
a finite mixture of a central measure and its injective branch pushforwards.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356.Splitting

variable {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α] [Fintype ι]

/-- A finite family of disjoint injective branches with strictly smaller
outer coefficients cannot support any preserving deterministic selector. -/
theorem no_preserving_splitMeasure_selection [MeasurableEq α]
    {ν : Measure α} [IsFiniteMeasure ν] {B : Set α}
    {H : ι → α → α} {c d : ℝ≥0∞}
    (hν : ν Set.univ ≠ 0) (hB : MeasurableSet B)
    (hfull : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i))
    (hInj : ∀ i, Set.InjOn (H i) B)
    (himage : ∀ i S, MeasurableSet S → S ⊆ B →
      MeasurableSet (H i '' S))
    (hCentral : ∀ i, Disjoint B (H i '' B))
    (hPair : Pairwise fun i j => Disjoint (H i '' B) (H j '' B))
    (hdc : d < c) :
    ¬ ∃ T : α → α, Measurable T ∧
      Measure.map T (splitMeasure ν c (fun _ => d) H) =
        splitMeasure ν c (fun _ => d) H ∧
      (∀ᵐ x ∂ν, ∃ i, T x = H i x) := by
  apply no_preserving_branch_selection hν hB hfull hH himage
  · intro S hS hSB
    exact splitMeasure_apply_central ν c (fun _ => d) H
      hfull hH hSB hS hCentral
  · intro i S hS hSB
    exact splitMeasure_apply_image ν c (fun _ => d) H
      hfull hH hInj hSB (fun j => himage j S hS hSB) hCentral hPair i
  · exact hdc

end Problem356.Splitting

end

end OAI
