import Mathlib
import OAI.Analysis.HardSphere.Geometry.GridNear
import OAI.Analysis.HardSphere.Geometry.AddedSites

namespace OAI

section

section
noncomputable section
open scoped Classical
namespace HardSphere.Comparison
open HardSphere.Lattice
variable {I V : Type*} [DecidableEq I]
def nearSlots (e : V→V→Prop) (c : I→V) (s t : Finset I) : Finset I :=
  s.filter (fun i ↦ ∃j∈t,e (c i) (c j))
def farSlots (e : V→V→Prop) (c : I→V) (s t : Finset I) : Finset I :=
  s\nearSlots e c s t
omit [DecidableEq I] in
lemma mem_nearSlots (e : V→V→Prop) (c : I→V) (s t : Finset I) (i : I) :
    i∈nearSlots e c s t ↔ i∈s ∧ ∃j∈t,e (c i) (c j) := by simp [nearSlots]
lemma mem_farSlots (e : V→V→Prop) (c : I→V) (s t : Finset I) (i : I) :
    i∈farSlots e c s t ↔ i∈s ∧ ∀j∈t,¬e (c i) (c j) := by
  simp [farSlots,nearSlots];tauto
lemma far_union_near (e : V→V→Prop) (c : I→V) (s t : Finset I) :
    farSlots e c s t∪nearSlots e c s t=s := by
  ext i
  simp [farSlots,nearSlots];tauto
lemma far_near_disjoint (e : V→V→Prop) (c : I→V) (s t : Finset I) :
    Disjoint (farSlots e c s t) (nearSlots e c s t) := Finset.sdiff_disjoint
lemma far_other_disjoint (e : V→V→Prop) (hrefl : ∀v,e v v) (c : I→V) (s t : Finset I) :
    Disjoint (farSlots e c s t) t := by
  apply Finset.disjoint_left.mpr
  intro i hi hit
  exact ((mem_farSlots e c s t i).mp hi).2 i hit (hrefl _)
lemma far_partition_disjoint (e : V→V→Prop) (hrefl : ∀v,e v v) (c : I→V) (s t : Finset I) :
    Disjoint (farSlots e c s t) (farSlots e c t s) ∧
    Disjoint (farSlots e c s t∪farSlots e c t s) (nearSlots e c s t∪nearSlots e c t s) := by
  have hst := far_other_disjoint e hrefl c s t
  have hts := far_other_disjoint e hrefl c t s
  have ns : nearSlots e c s t⊆s := Finset.filter_subset _ _
  have nt : nearSlots e c t s⊆t := Finset.filter_subset _ _
  have ft : farSlots e c t s⊆t := Finset.sdiff_subset
  refine ⟨hst.mono_right ft,?_⟩
  exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr
    ⟨far_near_disjoint e c s t,hst.mono_right nt⟩,
    Finset.disjoint_union_right.mpr ⟨hts.mono_right ns,far_near_disjoint e c t s⟩⟩
lemma route_partition_union (e : V→V→Prop) (c : I→V) (s t : Finset I) :
    (farSlots e c s t∪farSlots e c t s)∪(nearSlots e c s t∪nearSlots e c t s)=s∪t := by
  rw [Finset.union_union_union_comm,far_union_near,far_union_near]
omit [DecidableEq I] in
lemma nearSlots_card [DecidableEq V] (e : V→V→Prop) (c : I→V) (s t : Finset I)
    (hi : Set.InjOn c (s:Set I)) :
    (nearSlots e c s t).card≤(encounterSet e (s.image c) (t.image c)).card := by
  have hsub : (nearSlots e c s t).image c⊆
      (encounterSet e (s.image c) (t.image c)).image Prod.fst := by
    intro v hv
    obtain ⟨i,hi',rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨his,j,hjt,he⟩ := (mem_nearSlots e c s t i).mp hi'
    exact Finset.mem_image.mpr ⟨(c i,c j),(mem_encounterSet e _ _ _ _).mpr
      ⟨Finset.mem_image.mpr ⟨i,his,rfl⟩,Finset.mem_image.mpr ⟨j,hjt,rfl⟩,he⟩,rfl⟩
  have hin : Set.InjOn c (nearSlots e c s t:Set I) := hi.mono (Finset.filter_subset _ _)
  rw [←Finset.card_image_of_injOn hin]
  exact (Finset.card_le_card hsub).trans Finset.card_image_le
lemma commonSlots_near (e : V→V→Prop) (hrefl : ∀v,e v v) (c : I→V) (s t : Finset I) :
    nearSlots e c s t∩nearSlots e c t s=s∩t := by
  ext i
  simp only [Finset.mem_inter,mem_nearSlots]
  constructor
  · exact fun h ↦ ⟨h.1.1,h.2.1⟩
  · exact fun h ↦ ⟨⟨h.1,i,h.2,hrefl _⟩,⟨h.2,i,h.1,hrefl _⟩⟩

lemma physical_far_slots {K : ℕ} [NeZero K] (L : HardSphere.Length) (hL : L.val=(K:ℝ))
    (c : I→Fin 3→Fin K) (s t : Finset I) (i j : I)
    (hi : i∈farSlots (torusNear K 30) (fun i ↦ HardSphere.Groups.gridSite (c i)) s t)
    (hj : j∈t) :
    23<HardSphere.torusDistance L (HardSphere.CellOrbital.gridCenter L (c i)) (HardSphere.CellOrbital.gridCenter L (c j)) := by
  exact HardSphere.Groups.distance_far_of_grid_far L hL (by norm_num) _ _
    (((mem_farSlots _ _ _ _ _).mp hi).2 j hj)

end HardSphere.Comparison

end
end

section
noncomputable section
namespace HardSphere.Comparison
variable {J : Type*}

def routeEmbedding {d : ℕ} (labels : Fin d↪J) : Fin (d+1)↪Option J where
  toFun i := if h : i.val<d then some (labels ⟨i.val,h⟩) else none
  inj' := by
    intro i j hij
    by_cases hi : i.val<d <;> by_cases hj : j.val<d
    · simp only [dite_eq_left hi,dite_eq_left hj,Option.some.injEq] at hij
      have he := labels.injective hij
      exact Fin.ext (congrArg (fun k : Fin d ↦ k.val) he)
    · simp only [dite_eq_left hi,dite_eq_right hj] at hij
      contradiction
    · simp only [dite_eq_right hi,dite_eq_left hj] at hij
      contradiction
    · exact Fin.ext (by omega)
@[simp] lemma routeEmbedding_castSucc {d : ℕ} (labels : Fin d↪J) (i : Fin d) :
    routeEmbedding labels i.castSucc=some (labels i) := by
  change (if h : i.val<d then some (labels ⟨i.val,h⟩) else none)=_
  simp [i.isLt]
@[simp] lemma routeEmbedding_last {d : ℕ} (labels : Fin d↪J) :
    routeEmbedding labels (Fin.last d)=none := by
  change (if h : d<d then some (labels ⟨d,h⟩) else none)=_
  simp

def routePermutation {d : ℕ} (labels : Fin d↪J) : Equiv.Perm (Option J) :=
  (finRotate (d+1)).viaEmbedding (routeEmbedding labels)

def routeSlots {d : ℕ} (labels : Fin d↪J) : Finset (Option J) :=
  (Finset.univ.map (routeEmbedding labels))
lemma routePermutation_fixed {d : ℕ} (labels : Fin d↪J) (i : Option J)
    (hi : i∉routeSlots labels) : routePermutation labels i=i := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨j,rfl⟩
  apply hi
  exact Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩

lemma routePermutation_label {d : ℕ} (labels : Fin d↪J) (i : Fin d) :
    routePermutation labels (some (labels i))=routeEmbedding labels i.succ := by
  rw [←routeEmbedding_castSucc labels i]
  change (finRotate (d+1)).viaEmbedding (routeEmbedding labels) _=_
  rw [Equiv.Perm.viaEmbedding_apply]
  congr 1
  exact finRotate_of_lt i.isLt

lemma routePermutation_star (d : ℕ) (labels : Fin (d+1)↪J) :
    routePermutation labels none=some (labels 0) := by
  rw [←routeEmbedding_last labels]
  change (finRotate (d+1+1)).viaEmbedding (routeEmbedding labels) _=_
  rw [Equiv.Perm.viaEmbedding_apply,finRotate_last]
  exact routeEmbedding_castSucc labels 0

lemma routePermutation_lastLabel (d : ℕ) (labels : Fin (d+1)↪J) :
    routePermutation labels (some (labels (Fin.last d)))=none := by
  rw [routePermutation_label]
  exact routeEmbedding_last labels

lemma routeSlots_exact {d : ℕ} [DecidableEq J] (labels : Fin d↪J) :
    routeSlots labels=insert none (Finset.univ.image (fun i ↦ some (labels i))) := by
  ext x
  simp only [routeSlots,Finset.mem_map,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_image]
  constructor
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val<d
    · exact Or.inr ⟨⟨i.val,hi⟩,by change _=(if h : i.val<d then _ else _);rw [dite_eq_left hi]⟩
    · exact Or.inl (by change (if h : i.val<d then _ else _)=_;rw [dite_eq_right hi])
  · rintro (rfl|⟨i,rfl⟩)
    · exact ⟨Fin.last d,routeEmbedding_last labels⟩
    · exact ⟨i.castSucc,routeEmbedding_castSucc labels i⟩

end HardSphere.Comparison

end
end

end

end OAI
