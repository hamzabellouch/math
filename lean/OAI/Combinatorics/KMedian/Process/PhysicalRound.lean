import Mathlib
import OAI.Combinatorics.KMedian.Process.ForceBatchBound
import OAI.Combinatorics.KMedian.Process.GroupCap
import OAI.Combinatorics.KMedian.Process.CopyTransport

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F : Type*} [DecidableEq F] [Fintype F] {Δ : ℕ}

noncomputable def forcedGroups (A : Finset (Copy (F := F) Δ)) (H : Finset A) : Finset F :=
  H.image (fun i => i.val.1)

noncomputable def forcedAlive (A S : Finset (Copy (F := F) Δ)) (H : Finset A) : Finset A :=
  (localSet A S).filter (fun i => i.val.1 ∈ forcedGroups A H)

omit [Fintype F] in
 theorem forcedAlive_subset (A S : Finset (Copy (F := F) Δ)) (H : Finset A) :
    forcedAlive A S H ⊆ localSet A S := filter_subset _ _

omit [Fintype F] in
 theorem heavy_alive_forced (A S : Finset (Copy (F := F) Δ)) (H : Finset A) :
    H ∩ localSet A S ⊆ forcedAlive A S H := by
  intro i hi
  exact mem_filter.mpr ⟨(mem_inter.mp hi).2,
    mem_image.mpr ⟨i,(mem_inter.mp hi).1,rfl⟩⟩

noncomputable def roundAlive (A S : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) (x g : ℝ) (d : F → ℝ) :
    Finset (Copy (F := F) Δ) :=
  (nextAliveAt (heavyActions (graphActions G) H) (Analytic.coefficient x (mass g S))
    (fun i => d i.val.1) (localSet A S \ forcedAlive A S H) Z).image Subtype.val

 theorem nextAliveAt_subset_physical {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
    (D : Actions I E) (a : ℝ) (d : I → ℝ) (S : Finset I) (Z : Finset E) :
    nextAliveAt D a d S Z ⊆ physical D S Z := by
  unfold nextAliveAt
  split_ifs
  · exact retained_subset _ _ _ _
  · exact Subset.rfl

omit [Fintype F] in
 theorem roundAlive_subset (A S : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) (x g : ℝ) (d : F → ℝ) :
    roundAlive A S G H Z x g d ⊆ S := by
  rintro i hi
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
  exact (mem_localSet _ _ _).mp
    (sdiff_subset (nextAliveAt_subset _ _ _ _ _ hj))

omit [Fintype F] in
 theorem roundAlive_active (A S : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) (x g : ℝ) (d : F → ℝ) :
    roundAlive A S G H Z x g d ⊆ next Δ A (roundErased A G H Z) (roundOpened A G H Z) := by
  rintro i hi
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
  have hp := (mem_sdiff.mp (nextAliveAt_subset_physical _ _ _ _ _ hj)).2
  apply mem_union_left
  apply mem_sdiff.mpr
  refine ⟨j.property,?_⟩
  intro he
  obtain ⟨k,hk,hkj⟩ := mem_image.mp he
  exact hp ((Subtype.ext hkj) ▸ hk)

omit [Fintype F] in

theorem roundAlive_not_reset (A S : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) (x g : ℝ) (d : F → ℝ)
    (hown : ∀ i, own Δ A i ⊆ G i) {i : Copy (F := F) Δ}
    (hi : i ∈ roundAlive A S G H Z x g d) : i.1 ∉ roundOpened A G H Z := by
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
  have hp := mem_sdiff.mp (nextAliveAt_subset_physical _ _ _ _ _ hj)
  have hs := mem_sdiff.mp hp.1
  intro ho
  obtain ⟨s,hsource,hgroup⟩ := mem_image.mp ho
  rcases mem_union.mp hsource with hh | hh
  · have hhg : j.val.1 ∈ forcedGroups A H := mem_image.mpr ⟨s,hh,hgroup⟩
    exact hs.2 (mem_filter.mpr ⟨hs.1,hhg⟩)
  · obtain ⟨e,he,hes⟩ := mem_image.mp hh
    apply hp.2
    apply mem_biUnion.mpr
    refine ⟨e,(mem_inter.mp he).1,?_⟩
    have ho := (mem_inter.mp he).2
    have heq : (heavyActions (graphActions G) H).erase e=
        (graphActions G).erase ((heavyActions (graphActions G) H).source e) := by
      cases e with
      | inl e => rfl
      | inr e => simp [ordinary_heavyActions] at ho
    rw [heq]
    apply (mem_graph_erase G _ _).mpr
    apply hown j
    apply (mem_own Δ A _ _).mpr
    exact (congrArg (fun k : A => k.val.1) hes).trans hgroup

theorem round_cap (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) (R : ℝ) (d : F → ℝ)
    (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i) :
    GroupCap.cap R d (integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z)))=
      nextCap (heavyActions (graphActions G) H) (fun i => d i.val.1)
        (GroupCap.cap R d (integral Δ A ∪ forcedGroups A H)) Z := by
  rw [round_integral_eq Δ A G H Z hG hown]
  unfold roundOpened selectedSources
  rw [image_union,image_image,← union_assoc,GroupCap.cap_union_image]
  rfl

end MetricKMedian.CopyState
end
end

end OAI
