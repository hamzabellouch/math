import OAI.Combinatorics.InfiniteMatroid.PrototypeExtension
import OAI.Combinatorics.InfiniteMatroid.Matroid

namespace OAI

section
open Set Filter
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

def stagePrototypes : Option (Set E0) → Set Prototype
  | none => ∅
  | some B => prototypePair B
lemma stagePrototypes_finite (o : Option (Set E0)) : (stagePrototypes o).Finite := by
  cases o with
  | none => exact finite_empty
  | some B => exact prototypePair_finite B

def pastPrototypes (f : CIndex → Option (Set E0)) (a : CIndex) : Set Prototype :=
  ⋃ b : Iio a, stagePrototypes (f b)
def initialPrototypes (f : CIndex → Option (Set E0)) (a : CIndex) : Set Prototype :=
  pastPrototypes f a ∪ stagePrototypes (f a)
def allPrototypes (f : CIndex → Option (Set E0)) : Set Prototype :=
  ⋃ a, stagePrototypes (f a)

lemma stage_subset_past {f : CIndex → Option (Set E0)} {a b : CIndex} (h : b < a) :
    stagePrototypes (f b) ⊆ pastPrototypes f a := by
  intro p hp
  exact mem_iUnion.mpr ⟨⟨b,h⟩,hp⟩
lemma stage_subset_initial {f : CIndex → Option (Set E0)} {a b : CIndex} (h : b ≤ a) :
    stagePrototypes (f b) ⊆ initialPrototypes f a := by
  rcases h.lt_or_eq with h|rfl
  · exact (stage_subset_past h).trans subset_union_left
  · exact subset_union_right
lemma initial_subset_past {f : CIndex → Option (Set E0)} {a b : CIndex} (h : b < a) :
    initialPrototypes f b ⊆ pastPrototypes f a := by
  rintro p (hp|hp)
  · obtain ⟨c,hc⟩ := mem_iUnion.mp hp
    exact stage_subset_past (c.2.trans h) hc
  · exact stage_subset_past h hp
lemma initial_subset_all (f : CIndex → Option (Set E0)) (a : CIndex) :
    initialPrototypes f a ⊆ allPrototypes f := by
  rintro p (hp|hp)
  · obtain ⟨c,hc⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨c,hc⟩
  · exact mem_iUnion.mpr ⟨a,hp⟩
lemma past_cardinal (f : CIndex → Option (Set E0)) (a : CIndex) :
    Cardinal.mk (pastPrototypes f a) < Cardinal.continuum :=
  finite_union_small (cindex_predecessors a) _ (fun b ↦ stagePrototypes_finite (f b))

lemma exists_interval_enumeration :
    ∃ e : CIndex → (Set E0 × Set E0), Function.Surjective e := by
  classical
  obtain ⟨e,he⟩ := exists_set_enumeration (E0 × Bool)
  refine ⟨fun a ↦ ({x | (x,false) ∈ e a},{x | (x,true) ∈ e a}),?_⟩
  rintro ⟨I,Y⟩
  obtain ⟨a,ha⟩ := he {p | if p.2 then p.1 ∈ Y else p.1 ∈ I}
  exact ⟨a,by simp [ha]⟩

namespace RankModel
variable (R : RankModel D)

lemma good_past_of_initial (f : CIndex → Option (Set E0)) (a : CIndex)
    (h : ∀ b < a, R.GoodPrototypes (initialPrototypes f b)) :
    R.GoodPrototypes (pastPrototypes f a) := by
  constructor
  · intro p hp
    obtain ⟨b,hb⟩ := mem_iUnion.mp hp
    exact (h b b.2).admissible p (Or.inr hb)
  · intro p hp
    obtain ⟨b,hb⟩ := mem_iUnion.mp hp
    exact initial_subset_past b.2 ((h b b.2).flip_closed p (Or.inr hb))
  · intro p hp q hq hne
    obtain ⟨b,hb⟩ := mem_iUnion.mp hp
    obtain ⟨c,hc⟩ := mem_iUnion.mp hq
    have hg := h (max b.1 c.1) (max_lt b.2 c.2)
    exact hg.separated p (stage_subset_initial (le_max_left _ _) hb)
      q (stage_subset_initial (le_max_right _ _) hc) hne

lemma good_all_of_initial (f : CIndex → Option (Set E0))
    (h : ∀ a, R.GoodPrototypes (initialPrototypes f a)) :
    R.GoodPrototypes (allPrototypes f) := by
  constructor
  · intro p hp
    obtain ⟨a,ha⟩ := mem_iUnion.mp hp
    exact (h a).admissible p (Or.inr ha)
  · intro p hp
    obtain ⟨a,ha⟩ := mem_iUnion.mp hp
    exact initial_subset_all f a ((h a).flip_closed p (Or.inr ha))
  · intro p hp q hq hne
    obtain ⟨a,ha⟩ := mem_iUnion.mp hp
    obtain ⟨b,hb⟩ := mem_iUnion.mp hq
    exact (h (max a b)).separated p (stage_subset_initial (le_max_left _ _) ha)
      q (stage_subset_initial (le_max_right _ _) hb) hne

variable (hK : R.ideal = KIdeal)
include hK
lemma exists_stage (P : Set Prototype) (hP : R.GoodPrototypes P)
    (hcard : Cardinal.mk P < Cardinal.continuum) (I Y : Set E0) :
    ∃ o : Option (Set E0), R.GoodPrototypes (P ∪ stagePrototypes o) ∧
      (I ⊆ Y → Meets (PrototypeBases (P ∪ stagePrototypes o)) I Y) := by
  classical
  by_cases hIY : I ⊆ Y
  · by_cases hmet : Meets (PrototypeBases P) I Y
    · exact ⟨none,by simpa [stagePrototypes],by simpa [stagePrototypes] using (fun _ : I ⊆ Y ↦ hmet)⟩
    · obtain ⟨B,hB,hmet⟩ := R.extend_unmet hK hP hcard hIY hmet
      exact ⟨some B,hB,fun _ ↦ hmet⟩
  · exact ⟨none,by simpa [stagePrototypes],fun h ↦ (hIY h).elim⟩

noncomputable def assemblyStep (e : CIndex → (Set E0 × Set E0)) (a : CIndex)
    (f : Iio a → Option (Set E0)) : Option (Set E0) := by
  classical
  let P := ⋃ b : Iio a, stagePrototypes (f b)
  exact if h : R.GoodPrototypes P then
    Classical.choose (R.exists_stage hK P h
      (finite_union_small (cindex_predecessors a) _ (fun b ↦ stagePrototypes_finite (f b))) (e a).1 (e a).2)
    else none

noncomputable def assembled (e : CIndex → (Set E0 × Set E0)) : CIndex → Option (Set E0) :=
  wellFounded_lt.fix (fun a f ↦ R.assemblyStep hK e a (fun b ↦ f b b.2))

lemma assembled_eq (e : CIndex → (Set E0 × Set E0)) (a : CIndex) :
    R.assembled hK e a = R.assemblyStep hK e a (fun b ↦ R.assembled hK e b) :=
  WellFounded.fix_eq _ _ _

lemma assemblyStep_spec (e : CIndex → (Set E0 × Set E0)) (f : CIndex → Option (Set E0)) (a : CIndex)
    (h : R.GoodPrototypes (pastPrototypes f a)) :
    R.GoodPrototypes (pastPrototypes f a ∪ stagePrototypes (R.assemblyStep hK e a (fun b ↦ f b))) ∧
      ((e a).1 ⊆ (e a).2 →
        Meets (PrototypeBases (pastPrototypes f a ∪ stagePrototypes (R.assemblyStep hK e a (fun b ↦ f b))))
          (e a).1 (e a).2) := by
  classical
  unfold pastPrototypes at h ⊢
  simp only [assemblyStep,dite_eq_left h]
  exact Classical.choose_spec (R.exists_stage hK _ h
    (finite_union_small (cindex_predecessors a) _ (fun b ↦ stagePrototypes_finite (f b))) _ _)

lemma assembled_good_initial (e : CIndex → (Set E0 × Set E0)) (a : CIndex) :
    R.GoodPrototypes (initialPrototypes (R.assembled hK e) a) := by
  induction a using (wellFounded_lt (α := CIndex)).induction with
  | h a ih =>
    have hg := R.good_past_of_initial (R.assembled hK e) a ih
    have hs := (R.assemblyStep_spec hK e (R.assembled hK e) a hg).1
    change R.GoodPrototypes (pastPrototypes (R.assembled hK e) a ∪ stagePrototypes (R.assembled hK e a))
    rw [R.assembled_eq hK e a]
    exact hs

lemma assembled_meets (e : CIndex → (Set E0 × Set E0)) (a : CIndex)
    (hIY : (e a).1 ⊆ (e a).2) :
    Meets (PrototypeBases (allPrototypes (R.assembled hK e))) (e a).1 (e a).2 := by
  have hg := R.good_past_of_initial (R.assembled hK e) a
    (fun b _ ↦ R.assembled_good_initial hK e b)
  have hs := (R.assemblyStep_spec hK e (R.assembled hK e) a hg).2 hIY
  rw [← R.assembled_eq hK e a] at hs
  exact meets_mono (prototypeBases_mono (initial_subset_all _ _)) hs

/-- The continuum recursion meets every interval and preserves all old classes. -/
lemma exists_complete_prototypes : ∃ P : Set Prototype,
    R.GoodPrototypes P ∧ ∀ I Y, I ⊆ Y → Meets (PrototypeBases P) I Y := by
  obtain ⟨e,he⟩ := exists_interval_enumeration
  refine ⟨allPrototypes (R.assembled hK e),R.good_all_of_initial _ (R.assembled_good_initial hK e),?_⟩
  intro I Y hIY
  obtain ⟨a,ha⟩ := he (I,Y)
  have hs := R.assembled_meets hK e a (by simpa [ha] using hIY)
  simpa [ha] using hs

lemma exists_basisSystem : ∃ S : BasisSystem E0, ∀ B ∈ S.bases, R.Admissible B := by
  obtain ⟨P,hP,hmeet⟩ := R.exists_complete_prototypes hK
  obtain ⟨B,hB,_⟩ := hmeet ∅ univ (empty_subset _)
  refine ⟨⟨PrototypeBases P,⟨B,hB⟩,R.bases_antichain hP,R.bases_compl_closed hP,
    bases_swap,fun I Y hIY _ ↦ hmeet I Y hIY⟩,?_⟩
  intro B hB
  exact R.bases_admissible hK hP hB

end RankModel
end InfiniteMatroidCounterexample
end

end OAI
