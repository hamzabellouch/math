import OAI.Probability.ContinuumTransition.PhysicalPressure

namespace OAI

universe u_1 u_2

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
section
variable {X : Type u_1} [MeasurableSpace X] {ι : Type u_2} [Fintype ι] [DecidableEq ι]

omit [MeasurableSpace X] [Fintype ι] in
theorem binaryRegion_subset_union (A B : Set X) (s : Finset ι) :
    binaryRegion A B s ⊆ {x : ι → X | ∀ i, x i ∈ A ∪ B} := by
  intro x hx i
  by_cases hi : i ∈ s
  · exact Or.inl (by simpa only [ite_eq_left hi] using hx i)
  · exact Or.inr (by simpa only [ite_eq_right hi] using hx i)

omit [MeasurableSpace X] in

theorem iUnion_binaryRegion (A B : Set X) :
    (⋃ s : Finset ι, binaryRegion A B s) = {x : ι → X | ∀ i, x i ∈ A ∪ B} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    exact binaryRegion_subset_union A B s hs
  · intro hx
    refine mem_iUnion.mpr ⟨Finset.univ.filter (fun i => x i ∈ A), ?_⟩
    intro i
    by_cases hi : x i ∈ A
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_left hi] using hi
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_right hi] using
        (hx i).resolve_left hi

theorem integral_binary_assignments_eq (μ : Measure X) [SigmaFinite μ]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    {F : (ι → X) → ℝ}
    (hF : IntegrableOn F {x : ι → X | ∀ i, x i ∈ A ∪ B} (Measure.pi (fun _ : ι => μ))) :
    (∫ x in {x : ι → X | ∀ i, x i ∈ A ∪ B}, F x ∂(Measure.pi (fun _ : ι => μ))) =
      ∑ s : Finset ι, ∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  have hh := integral_biUnion_finset (Finset.univ : Finset (Finset ι))
    (fun s _ => measurableSet_binaryRegion hA hB s)
    (fun _ _ _ _ hne => binaryRegion_pairwiseDisjoint hd hne)
    (fun s _ => hF.mono_set (binaryRegion_subset_union A B s))
  simpa only [Finset.mem_univ, iUnion_true, iUnion_binaryRegion] using hh

end
end ContinuumTemperature
end

end OAI
