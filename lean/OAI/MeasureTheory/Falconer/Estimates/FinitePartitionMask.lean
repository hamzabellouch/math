import OAI.MeasureTheory.Falconer.Estimates.PrunedVariation

namespace OAI

/-! # Bounded measurable masks on a finite disjoint spatial partition -/

namespace Falconer
open Set MeasureTheory
variable {X ι : Type*} [MeasurableSpace X]

noncomputable def finitePartitionMask (F : Finset ι) (C : ι → Set X) (w : ι → X → ℝ) : X → ℝ :=
  fun x => ∑ i ∈ F, (C i).indicator (w i) x

 theorem finitePartitionMask_measurable (F : Finset ι) (C : ι → Set X) (w : ι → X → ℝ)
    (hC : ∀ i ∈ F, MeasurableSet (C i)) (hw : ∀ i ∈ F, Measurable (w i)) :
    Measurable (finitePartitionMask F C w) :=
  Finset.measurable_sum F (fun i hi => (hw i hi).indicator (hC i hi))

omit [MeasurableSpace X] in
 theorem finitePartitionMask_on (F : Finset ι) (C : ι → Set X) (w : ι → X → ℝ)
    (hdis : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (C i) (C j))
    {i : ι} (hi : i ∈ F) {x : X} (hx : x ∈ C i) :
    finitePartitionMask F C w x = w i x := by
  classical
  unfold finitePartitionMask
  rw [Finset.sum_eq_single_of_mem i hi]
  · exact indicator_of_mem hx _
  · intro j hj hji
    apply indicator_of_notMem
    intro hjx
    exact Set.disjoint_left.mp (hdis i hi j hj hji.symm) hx hjx

omit [MeasurableSpace X] in
 theorem finitePartitionMask_off (F : Finset ι) (C : ι → Set X) (w : ι → X → ℝ)
    {x : X} (hx : x ∉ ⋃ i ∈ F, C i) : finitePartitionMask F C w x = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact indicator_of_notMem (fun hxi => hx (mem_iUnion₂.mpr ⟨i,hi,hxi⟩)) _

omit [MeasurableSpace X] in
 theorem finitePartitionMask_bounds (F : Finset ι) (C : ι → Set X) (w : ι → X → ℝ)
    (hdis : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (C i) (C j))
    (hw : ∀ i ∈ F, ∀ x, w i x ∈ Icc (0:ℝ) 1) (x : X) :
    finitePartitionMask F C w x ∈ Icc (0:ℝ) 1 := by
  by_cases hx : x ∈ ⋃ i ∈ F, C i
  · obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hx
    rw [finitePartitionMask_on F C w hdis hi hxi]
    exact hw i hi x
  · rw [finitePartitionMask_off F C w hx]
    exact ⟨le_rfl,zero_le_one⟩

end Falconer

end OAI
