import Mathlib

namespace OAI

universe uAlpha uBeta

noncomputable section

open MeasureTheory Set

namespace Problem356
namespace LocalBranchMeasure

variable {α : Type uAlpha} {β : Type uBeta} [TopologicalSpace α] [TopologicalSpace β]
  [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α] [BorelSpace β]

/-- A local branch extended by a fixed value outside its source. -/
def extendedBranch (e : OpenPartialHomeomorph α β) (z : β) : α → β := by
  classical
  exact e.source.piecewise e (fun _ => z)

omit [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α] [BorelSpace β] in
@[simp] theorem extendedBranch_apply_of_mem
    (e : OpenPartialHomeomorph α β) (z : β) {x : α} (hx : x ∈ e.source) :
    extendedBranch e z x = e x := by
  classical
  simp [extendedBranch, hx]

/-- The extension is Borel measurable even if the local map is arbitrary outside its source. -/
theorem measurable_extendedBranch (e : OpenPartialHomeomorph α β) (z : β) :
    Measurable (extendedBranch e z) := by
  classical
  exact e.continuousOn.measurable_piecewise continuous_const.continuousOn
    e.open_source.measurableSet

/-- Restricting the domain of a local branch to a measurable set gives a measurable image. -/
theorem measurableSet_image (e : OpenPartialHomeomorph α β)
    {S : Set α} (hS : MeasurableSet S) (hSub : S ⊆ e.source) :
    MeasurableSet (e '' S) := by
  have h := e.isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image'
    (hS.preimage measurable_subtype_coe)
  simpa only [Set.image_domRestrict, Set.inter_eq_left.mpr hSub] using h

omit [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α] [BorelSpace β] in
/-- Extension preserves every image of a subset of the local source. -/
theorem extendedBranch_image (e : OpenPartialHomeomorph α β) (z : β)
    {S : Set α} (hSub : S ⊆ e.source) :
    extendedBranch e z '' S = e '' S := by
  apply Set.image_congr
  intro x hx
  exact extendedBranch_apply_of_mem e z (hSub hx)

/-- Measurability of selected branch images required by deterministic-selection obstructions. -/
theorem measurableSet_extendedBranch_image (e : OpenPartialHomeomorph α β) (z : β)
    {S : Set α} (hS : MeasurableSet S) (hSub : S ⊆ e.source) :
    MeasurableSet (extendedBranch e z '' S) := by
  rw [extendedBranch_image e z hSub]
  exact measurableSet_image e hS hSub

omit [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α] [BorelSpace β] in
/-- Injectivity of the extension on any subset of the source. -/
theorem injOn_extendedBranch (e : OpenPartialHomeomorph α β) (z : β)
    {B : Set α} (hB : B ⊆ e.source) : InjOn (extendedBranch e z) B := by
  intro x hx y hy hxy
  apply e.injOn (hB hx) (hB hy)
  simpa only [extendedBranch_apply_of_mem e z (hB hx),
    extendedBranch_apply_of_mem e z (hB hy)] using hxy

omit [BorelSpace α] [BorelSpace β] in
/-- Extending outside the source does not change pushforwards of measures concentrated there. -/
theorem map_extendedBranch (e : OpenPartialHomeomorph α β) (z : β)
    (ν : Measure α) (hν : ∀ᵐ x ∂ν, x ∈ e.source) :
    Measure.map (extendedBranch e z) ν = Measure.map e ν := by
  apply Measure.map_congr
  filter_upwards [hν] with x hx
  exact extendedBranch_apply_of_mem e z hx

/-- A measurable selector's coincidence set with an extended local branch is measurable. -/
theorem measurableSet_selection [MeasurableEq β]
    (e : OpenPartialHomeomorph α β) (z : β) {B : Set α}
    (hB : MeasurableSet B) {T : α → β} (hT : Measurable T) :
    MeasurableSet (B ∩ {x | T x = extendedBranch e z x}) :=
  hB.inter (measurableSet_eq_fun hT (measurable_extendedBranch e z))

/-- Selected coincidence sets have measurable branch images. -/
theorem measurableSet_selection_image [MeasurableEq β]
    (e : OpenPartialHomeomorph α β) (z : β) {B : Set α}
    (hB : MeasurableSet B) (hSub : B ⊆ e.source)
    {T : α → β} (hT : Measurable T) :
    MeasurableSet (extendedBranch e z '' (B ∩ {x | T x = extendedBranch e z x})) := by
  apply measurableSet_extendedBranch_image e z (measurableSet_selection e z hB hT)
  exact inter_subset_left.trans hSub

end LocalBranchMeasure
end Problem356

end

end OAI
