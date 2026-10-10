import Mathlib
import OAI.Combinatorics.KMedian.Process.CopyState
import OAI.Combinatorics.KMedian.Process.ActualActions

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset FixedBatch
variable {F : Type*} [DecidableEq F] [Fintype F] (Δ : ℕ)

noncomputable def own (A : Finset (Copy (F := F) Δ)) (i : A) : Finset A :=
  univ.filter (fun h => h.val.1=i.val.1)

omit [Fintype F] in
@[simp] theorem mem_own (A : Finset (Copy (F := F) Δ)) (i h : A) :
    h ∈ own Δ A i ↔ h.val.1=i.val.1 := by simp [own]

omit [Fintype F] in
 theorem own_card_le (A : Finset (Copy (F := F) Δ)) (i : A) : (own Δ A i).card ≤ Δ := by
  have hc : (own Δ A i).image Subtype.val ⊆ slots Δ i.val.1 := by
    rintro h hh
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hh
    exact (mem_slots _ _ _).mpr ((mem_own _ _ _ _).mp ht)
  have hh := card_le_card hc
  rw [card_image_of_injective _ Subtype.val_injective,card_slots] at hh
  exact hh

 theorem own_card_integral (A : Finset (Copy (F := F) Δ)) (i : A)
    (hi : i.val.1 ∈ integral Δ A) : (own Δ A i).card=Δ := by
  have he : (own Δ A i).image Subtype.val=slots Δ i.val.1 := by
    ext h
    constructor
    · intro hh
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hh
      exact (mem_slots _ _ _).mpr ((mem_own _ _ _ _).mp ht)
    · intro hh
      have hA := (mem_integral _ _ _).mp hi hh
      exact mem_image.mpr ⟨⟨h,hA⟩,(mem_own _ _ _ _).mpr ((mem_slots _ _ _).mp hh),rfl⟩
  have hc := congrArg Finset.card he
  simpa only [card_image_of_injective _ Subtype.val_injective,card_slots] using hc

 theorem integral_incoming_same_group (A : Finset (Copy (F := F) Δ))
    (G : A → Finset A) (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i)
    {i h : A} (hi : i.val.1 ∈ integral Δ A) (hh : h ∈ G i) : h.val.1=i.val.1 := by
  have he : own Δ A i=G i := eq_of_subset_of_card_le (hown i)
    (by rw [hG i,own_card_integral Δ A i hi])
  exact (mem_own _ _ _ _).mp (he.symm ▸ hh)

variable {Δ}

 theorem heavy_erase_parent {I : Type*} [Fintype I] [DecidableEq I]
    (Full : Actions I I) (H : Finset I) (e : HeavyAction Full H) :
    (heavyActions Full H).erase e ⊆ Full.erase (heavyParent Full H e) := by
  intro i hi
  cases e with
  | inl h => exact hi
  | inr p => exact (mem_singleton.mp hi).symm ▸ p.property.2

noncomputable def selectedSources {I : Type*} [Fintype I] [DecidableEq I]
    (G : I → Finset I) (H : Finset I) (Z : Finset (HeavyAction (graphActions G) H)) : Finset I :=
  H ∪ (Z ∩ (heavyActions (graphActions G) H).ordinary).image
    (heavyActions (graphActions G) H).source

 theorem parent_selected {I : Type*} [Fintype I] [DecidableEq I]
    (G : I → Finset I) (H : Finset I) (Z : Finset (HeavyAction (graphActions G) H))
    {e : HeavyAction (graphActions G) H} (he : e ∈ Z) :
    heavyParent (graphActions G) H e ∈ selectedSources G H Z := by
  by_cases ho : e ∈ (heavyActions (graphActions G) H).ordinary
  · exact mem_union_right _ (mem_image.mpr ⟨e,mem_inter.mpr ⟨he,ho⟩,rfl⟩)
  · exact mem_union_left _ (nonordinary_parent_heavy G H e ho)

noncomputable def roundErased (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) : Finset (Copy (F := F) Δ) :=
  (Z.biUnion (heavyActions (graphActions G) H).erase).image Subtype.val

noncomputable def roundOpened (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) : Finset F :=
  (selectedSources G H Z).image (fun i => i.val.1)

omit [Fintype F] in
 theorem roundErased_subset (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) : roundErased A G H Z ⊆ A := by
  rintro i hi
  obtain ⟨h,_,rfl⟩ := mem_image.mp hi
  exact h.property

omit [Fintype F] in
 theorem roundErased_nonempty (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H))
    (he : (roundErased A G H Z).Nonempty) : (roundOpened A G H Z).Nonempty := by
  obtain ⟨i,hi⟩ := he
  obtain ⟨j,hj,_⟩ := mem_image.mp hi
  obtain ⟨e,he,_⟩ := mem_biUnion.mp hj
  exact ⟨_,mem_image.mpr ⟨_,parent_selected G H Z he,rfl⟩⟩

 theorem round_integral_persists (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H))
    (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i) :
    integral Δ A ⊆ integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z)) := by
  apply integral_persists
  intro i _ hie hii
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hie
  obtain ⟨e,he,hje⟩ := mem_biUnion.mp hj
  have hp := heavy_erase_parent (graphActions G) H e hje
  have hg := (mem_graph_erase G _ _).mp hp
  have hsame := integral_incoming_same_group Δ A G hG hown hii hg
  exact mem_image.mpr ⟨_,parent_selected G H Z he,hsame⟩

omit [Fintype F] in
 theorem round_mass_at_least_one (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) {g : ℝ}
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (hA : 1 ≤ PhysicalPotential.mass g A) :
    1 ≤ PhysicalPotential.mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z)) :=
  next_mass_at_least_one Δ A _ _ hg hunit hA (roundErased_nonempty A G H Z)

end MetricKMedian.CopyState
end
end

end OAI
