import Mathlib

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology
namespace LocalAE
variable {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] (μ : Measure α)

def region (P : α → Prop) : Set α :=
  {x | ∃U : Set α, IsOpen U ∧ x∈U ∧ ∀ᵐ y ∂μ.restrict U, P y}

lemma isOpen_region (P : α → Prop) : IsOpen (region μ P) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨U,hU,hx,hP⟩
  apply mem_of_superset (hU.mem_nhds hx)
  intro y hy
  exact ⟨U,hU,hy,hP⟩

lemma ae_region [SecondCountableTopology α] (P : α → Prop) :
    ∀ᵐ x ∂μ.restrict (region μ P), P x := by
  let I := {U : Set α // IsOpen U ∧ ∀ᵐ x ∂μ.restrict U,P x}
  have he : region μ P=⋃U : I,U.val := by
    ext x
    simp only [region,mem_ofPred_eq,mem_iUnion]
    constructor
    · rintro ⟨U,hU,hx,hP⟩
      exact ⟨⟨U,hU,hP⟩,hx⟩
    · rintro ⟨U,hx⟩
      exact ⟨U.val,U.property.1,hx,U.property.2⟩
  obtain ⟨T,hT,heT⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun U : I ↦ U.val) (fun U ↦ U.property.1)
  rw [he,←heT,ae_restrict_biUnion_iff _ hT]
  intro U hU
  exact U.property.2

lemma region_unique [IsOpenPosMeasure μ] {f : α → β} {z w : β} {x : α}
    (hz : x∈region μ (fun y ↦ f y=z)) (hw : x∈region μ (fun y ↦ f y=w)) : z=w := by
  obtain ⟨U,hU,hx,hz⟩ := hz
  obtain ⟨V,hV,hy,hw⟩ := hw
  have hne := (hU.inter hV).measure_ne_zero μ ⟨x,hx,hy⟩
  have hp : ∀ᵐ y ∂μ.restrict (U∩V), f y=z ∧ f y=w :=
    (ae_restrict_of_ae_restrict_of_subset inter_subset_left hz).and
      (ae_restrict_of_ae_restrict_of_subset inter_subset_right hw)
  obtain ⟨y,hy,h1,h2⟩ := exists_mem_of_measure_ne_zero_of_ae hne hp
  exact h1.symm.trans h2

lemma connected_region [IsOpenPosMeasure μ] {f : α → β} {S : Set α}
    (hS : IsPreconnected S) (hcover : ∀x∈S, ∃z, x∈region μ (fun y ↦ f y=z))
    {x : α} (hx : x∈S) {z : β} (hz : x∈region μ (fun y ↦ f y=z)) :
    S⊆region μ (fun y ↦ f y=z) := by
  let U := region μ (fun y ↦ f y=z)
  let V := ⋃w≠z,region μ (fun y ↦ f y=w)
  have hU : IsOpen U := isOpen_region μ _
  have hV : IsOpen V := isOpen_iUnion (fun w ↦ isOpen_iUnion (fun _ ↦ isOpen_region μ _))
  have hd : Disjoint U V := by
    apply disjoint_left.mpr
    intro y hy hyv
    obtain ⟨w,hw'⟩ := mem_iUnion.mp hyv
    obtain ⟨hw,hy'⟩ := mem_iUnion.mp hw'
    exact hw (region_unique μ hy' hy)
  have hc : S⊆U∪V := by
    intro y hy
    obtain ⟨w,hw⟩ := hcover y hy
    by_cases he : w=z
    · exact Or.inl (by simpa only [U,he] using hw)
    · exact Or.inr (mem_iUnion.mpr ⟨w,mem_iUnion.mpr ⟨he,hw⟩⟩)
  exact hS.subset_left_of_subset_union hU hV hd hc ⟨x,hx,hz⟩

omit [TopologicalSpace α] in
lemma ae_local_const_of_ae_pairs {f : α → β} {U : Set α} (hU : μ U≠0)
    (h : ∀ᵐ x ∂μ.restrict U, ∀ᵐ y ∂μ.restrict U,f x=f y) :
    ∃z,∀ᵐ y ∂μ.restrict U,f y=z := by
  obtain ⟨x,hx,hp⟩ := exists_mem_of_measure_ne_zero_of_ae hU h
  exact ⟨f x,hp.mono (fun _ hy ↦ hy.symm)⟩

def representative [Inhabited β] (f : α → β) (x : α) : β := by
  classical
  exact if h : ∃z,x∈region μ (fun y ↦ f y=z) then Classical.choose h else default

lemma representative_mem [Inhabited β] {f : α → β} {x : α}
    (h : ∃z,x∈region μ (fun y ↦ f y=z)) :
    x∈region μ (fun y ↦ f y=representative μ f x) := by
  simp only [representative,dite_eq_left h]
  exact Classical.choose_spec h

lemma representative_eq [Inhabited β] [IsOpenPosMeasure μ] {f : α → β} {x : α} {z : β}
    (h : x∈region μ (fun y ↦ f y=z)) : representative μ f x=z :=
  region_unique μ (representative_mem μ ⟨z,h⟩) h

lemma representative_ae [Inhabited β] [IsOpenPosMeasure μ] [SecondCountableTopology α]
    [OpensMeasurableSpace α] {f : α → β} {S : Set α} (hS : IsOpen S)
    (hcover : ∀x∈S,∃z,x∈region μ (fun y ↦ f y=z)) :
    ∀ᵐ x ∂μ.restrict S,f x=representative μ f x := by
  have hsub : S⊆region μ (fun y ↦ f y=representative μ f y) := by
    intro x hx
    obtain ⟨z,U,hU,hxU,hf⟩ := hcover x hx
    refine ⟨U∩S,hU.inter hS,⟨hxU,hx⟩,?_⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hf,
      ae_restrict_mem (hU.inter hS).measurableSet] with y hy hym
    exact hy.trans (representative_eq μ (show y∈region μ (fun y ↦ f y=z) from ⟨U,hU,hym.1,hf⟩)).symm
  exact ae_restrict_of_ae_restrict_of_subset hsub (ae_region μ _)

lemma representative_eq_on_connected [Inhabited β] [IsOpenPosMeasure μ]
    {f : α → β} {S : Set α} (hS : IsPreconnected S)
    (hcover : ∀x∈S,∃z,x∈region μ (fun y ↦ f y=z)) {x y : α} (hx : x∈S) (hy : y∈S) :
    representative μ f x=representative μ f y := by
  have hz := representative_mem μ (hcover x hx)
  have hzy := connected_region μ hS hcover hx hz hy
  exact (representative_eq μ hzy).symm

end LocalAE

end
end

end

end OAI
