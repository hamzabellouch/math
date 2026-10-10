import OAI.Probability.MatroidProphet.Groups
import OAI.Probability.MatroidProphet.Residual.Statistics
import OAI.Probability.MatroidProphet.ProductSplit

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def trueGroup (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) : Finset (Fin n) :=
  univ.filter fun e => candidate M d s e (s e) ∧ s e = some i

@[simp] lemma mem_trueGroup (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (e : Fin n) :
    e ∈ trueGroup M d s i ↔ candidate M d s e (s e) ∧ s e = some i := by
  simp [trueGroup]

lemma trueGroup_disjoint (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) : Pairwise (fun i j => Disjoint (trueGroup M d s i) (trueGroup M d s j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro e hei hej
  exact hij (Option.some.inj (((mem_trueGroup M d s i e).mp hei).2.symm.trans
    ((mem_trueGroup M d s j e).mp hej).2))

lemma trueGroup_disjoint_H (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) : Disjoint (trueGroup M d s i) d.H := by
  apply disjoint_left.mpr
  intro e he hh
  exact ((mem_trueGroup M d s i e).mp he).1.2.1 hh

lemma mem_listed_iff (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) :
    i ∈ listed M d s ↔ ∃ e ∈ d.D, e ∈ trueGroup M d s i := by
  simp only [listed, mem_biUnion, mem_trueGroup]
  constructor
  · rintro ⟨e, he, hi⟩
    by_cases hc : candidate M d s e (s e)
    · simp only [ite_eq_left hc, Option.mem_toFinset] at hi
      exact ⟨e, he, hc, hi⟩
    · simp only [ite_eq_right hc, Finset.notMem_empty] at hi
  · rintro ⟨e, he, hc, hi⟩
    exact ⟨e, he, by rw [ite_eq_left hc]; simp [hi]⟩

def withMasks (d : MainMasks n) (A B C : Finset (Fin n)) : MainMasks n :=
  { d with D := A, C := B, T := C }

@[simp] lemma candidate_withMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (A B C : Finset (Fin n)) (s : Fin n → Option ℤ) (e : Fin n) (v : Option ℤ) :
    candidate M (withMasks d A B C) s e v ↔ candidate M d s e v := Iff.rfl

@[simp] lemma trueGroup_withMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (A B C : Finset (Fin n)) (s : Fin n → Option ℤ) (i : ℤ) :
    trueGroup M (withMasks d A B C) s i = trueGroup M d s i := rfl

lemma groups_withMasks_guards (M : Matroid (Fin n)) (d : MainMasks n)
    (A B C B' C' : Finset (Fin n)) (s : Fin n → Option ℤ) :
    groups M (withMasks d A B C) s = groups M (withMasks d A B' C') s := rfl

def focalMasks (d : MainMasks n) (U A B C : Finset (Fin n)) : MainMasks n :=
  { d with D := (d.D \ U) ∪ A, C := (d.C \ U) ∪ B, T := (d.T \ U) ∪ C }

@[simp] lemma candidate_focalMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (U A B C : Finset (Fin n)) (s : Fin n → Option ℤ) (e : Fin n) (v : Option ℤ) :
    candidate M (focalMasks d U A B C) s e v ↔ candidate M d s e v := Iff.rfl

@[simp] lemma trueGroup_focalMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (U A B C : Finset (Fin n)) (s : Fin n → Option ℤ) (i : ℤ) :
    trueGroup M (focalMasks d U A B C) s i = trueGroup M d s i := rfl

lemma listed_focalMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) :
    listed M (focalMasks d (trueGroup M d s i) A B C) s =
      (listed M d s \ {i}) ∪ (if A.Nonempty then {i} else ∅) := by
  ext j
  rw [mem_listed_iff]
  simp only [focalMasks, mem_union, mem_sdiff,
    mem_singleton, mem_listed_iff]
  by_cases hne : A.Nonempty
  · simp only [ite_eq_left hne, mem_singleton]
    constructor
    · rintro ⟨e, he | he, hej⟩
      · refine Or.inl ⟨⟨e, he.1, hej⟩, ?_⟩
        intro hji
        exact he.2 (hji ▸ hej)
      · exact Or.inr (Option.some.inj
          (((mem_trueGroup M d s j e).mp hej).2.symm.trans
            ((mem_trueGroup M d s i e).mp (hA he)).2))
    · rintro (⟨⟨e, heD, hej⟩, hji⟩ | rfl)
      · refine ⟨e, Or.inl ⟨heD, ?_⟩, hej⟩
        intro hei
        exact hji (Option.some.inj
          (((mem_trueGroup M d s j e).mp hej).2.symm.trans
            ((mem_trueGroup M d s i e).mp hei).2))
      · obtain ⟨e, he⟩ := hne
        exact ⟨e, Or.inr he, hA he⟩
  · simp only [ite_eq_right hne, Finset.notMem_empty, or_false]
    constructor
    · rintro ⟨e, he | he, hej⟩
      · refine ⟨⟨e, he.1, hej⟩, ?_⟩
        intro hji
        exact he.2 (hji ▸ hej)
      · exact False.elim (hne ⟨e, he⟩)
    · rintro ⟨⟨e, heD, hej⟩, hji⟩
      refine ⟨e, Or.inl ⟨heD, ?_⟩, hej⟩
      intro hei
      exact hji (Option.some.inj
        (((mem_trueGroup M d s j e).mp hej).2.symm.trans
          ((mem_trueGroup M d s i e).mp hei).2))

noncomputable def focalReference (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) : MainMasks n :=
  focalMasks d (trueGroup M d s i) (trueGroup M d s i) ∅ ∅

lemma groups_focalMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty) :
    groups M (focalMasks d (trueGroup M d s i) A B C) s =
      groups M (focalReference M d s i) s := by
  have hU : (trueGroup M d s i).Nonempty := hne.mono hA
  unfold groups focalReference
  rw [listed_focalMasks M d s i A B C hA,
    listed_focalMasks M d s i _ ∅ ∅ Subset.rfl, ite_eq_left hne, ite_eq_left hU]

lemma focal_mem_reference_groups (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (hU : (trueGroup M d s i).Nonempty) :
    i ∈ groups M (focalReference M d s i) s := by
  rw [mem_groups]
  unfold focalReference
  rw [listed_focalMasks M d s i _ ∅ ∅ Subset.rfl, ite_eq_left hU]
  exact mem_union_right _ (mem_singleton_self i)

lemma groupMask_at_key (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (mask : Finset (Fin n)) (h : ℕ) (i : ℤ)
    (hi : (groups M d s)[h]? = some i) :
    groupMask M d s mask h = ((mask ∩ trueGroup M d s i : Finset (Fin n)) : Set (Fin n)) := by
  ext e
  simp only [groupMask, Set.mem_ofPred_eq, Finset.mem_coe, mem_inter, mem_trueGroup, hi]

lemma replaceMask_inter_self (X U A : Finset (Fin n)) (hA : A ⊆ U) :
    ((X \ U) ∪ A) ∩ U = A := by
  ext e
  simp only [mem_inter, mem_union, mem_sdiff]
  constructor
  · rintro ⟨he | he, heU⟩
    · exact False.elim (he.2 heU)
    · exact he
  · intro he
    exact ⟨Or.inr he, hA he⟩

lemma replaceMask_inter_other (X U A V : Finset (Fin n))
    (hA : A ⊆ U) (hUV : Disjoint U V) :
    ((X \ U) ∪ A) ∩ V = X ∩ V := by
  ext e
  simp only [mem_inter, mem_union, mem_sdiff]
  constructor
  · rintro ⟨he | he, heV⟩
    · exact ⟨he.1, heV⟩
    · exact False.elim (disjoint_left.mp hUV (hA he) heV)
  · rintro ⟨heX, heV⟩
    exact ⟨Or.inl ⟨heX, fun heU => disjoint_left.mp hUV heU heV⟩, heV⟩

noncomputable def focalIndex (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) : ℕ :=
  (groups M (focalReference M d s i) s).idxOf i

lemma focal_group_key (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty) :
    (groups M (focalMasks d (trueGroup M d s i) A B C) s)[focalIndex M d s i]? = some i := by
  rw [groups_focalMasks M d s i A B C hA hne]
  exact groups_get?_idxOf M _ s i (focal_mem_reference_groups M d s i (hne.mono hA))

lemma focal_group_mask (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C X Y : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty)
    (hY : Y ⊆ trueGroup M d s i) :
    groupMask M (focalMasks d (trueGroup M d s i) A B C) s
      ((X \ trueGroup M d s i) ∪ Y) (focalIndex M d s i) = (Y : Set (Fin n)) := by
  rw [groupMask_at_key M _ s _ _ i (focal_group_key M d s i A B C hA hne),
    trueGroup_focalMasks, replaceMask_inter_self X _ Y hY]

lemma lower_group_mask (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C X Y Z : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty)
    (hY : Y ⊆ trueGroup M d s i) (hZ : Z ⊆ trueGroup M d s i)
    (j : ℕ) (hj : j < focalIndex M d s i) :
    groupMask M (focalMasks d (trueGroup M d s i) A B C) s
      ((X \ trueGroup M d s i) ∪ Y) j =
    groupMask M (focalReference M d s i) s
      ((X \ trueGroup M d s i) ∪ Z) j := by
  have hi := groups_get?_idxOf M (focalReference M d s i) s i
    (focal_mem_reference_groups M d s i (hne.mono hA))
  obtain ⟨k, hk, hki⟩ := groups_earlier_key M (focalReference M d s i) s hi hj
  have hk' : (groups M (focalMasks d (trueGroup M d s i) A B C) s)[j]? = some k := by
    rwa [groups_focalMasks M d s i A B C hA hne]
  have hdisj := trueGroup_disjoint M d s (ne_of_gt hki)
  rw [groupMask_at_key M _ s _ j k hk', groupMask_at_key M _ s _ j k hk]
  simp only [focalReference, trueGroup_focalMasks]
  rw [replaceMask_inter_other X _ Y _ hY hdisj,
    replaceMask_inter_other X _ Z _ hZ hdisj]

end MatroidProphet.MainAlgorithm

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

lemma guardedPath_congr_prefix (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C D' C' : ℕ → Set α) (h : ℕ)
    (hD : ∀ j < h, D j = D' j) (hC : ∀ j < h, C j = C' j) (k : ℤ) :
    guardedPath M hE κ D C h k = guardedPath M hE κ D' C' h k := by
  induction h generalizing k with
  | zero => rfl
  | succ h ih =>
    simp only [guardedPath, hD h (Nat.lt_succ_self h), hC h (Nat.lt_succ_self h),
      ih (fun j hj => hD j (Nat.lt_succ_of_lt hj)) (fun j hj => hC j (Nat.lt_succ_of_lt hj))]

lemma nominalPath_congr_prefix (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C D' C' : ℕ → Set α) (h : ℕ)
    (hD : ∀ j ≤ h, D j = D' j) (hC : ∀ j < h, C j = C' j) (k : ℤ) :
    nominalPath M hE κ D C h k = nominalPath M hE κ D' C' h k := by
  rw [nominalPath, nominalPath, hD h le_rfl,
    guardedPath_congr_prefix M hE κ D C D' C' h (fun j hj => hD j hj.le) hC k]

lemma lowerCompetition_congr_prefix (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C T D' C' T' : ℕ → Set α) (h : ℕ)
    (hD : ∀ j < h, D j = D' j) (hC : ∀ j < h, C j = C' j)
    (hT : ∀ j < h, T j = T' j) (k : ℤ) :
    lowerCompetition M hE κ D C T k h = lowerCompetition M hE κ D' C' T' k h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [lowerCompetition, lowerCompetition, hT h (Nat.lt_succ_self h),
      ih (fun j hj => hD j (Nat.lt_succ_of_lt hj)) (fun j hj => hC j (Nat.lt_succ_of_lt hj))
        (fun j hj => hT j (Nat.lt_succ_of_lt hj)),
      nominalPath_congr_prefix M hE κ D C D' C' h
        (fun j hj => hD j (Nat.lt_succ_of_le hj)) (fun j hj => hC j (Nat.lt_succ_of_lt hj)),
      nominalPath_congr_prefix M hE κ D C D' C' h
        (fun j hj => hD j (Nat.lt_succ_of_le hj)) (fun j hj => hC j (Nat.lt_succ_of_lt hj))]

namespace MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma focal_prefix_masks (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) (hne : A.Nonempty)
    (j : ℕ) (hj : j < focalIndex M d s i) :
    let f := focalMasks d (trueGroup M d s i) A B C
    let r := focalReference M d s i
    groupMask M f s f.D j = groupMask M r s r.D j ∧
    groupMask M f s f.C j = groupMask M r s r.C j ∧
    groupMask M f s f.T j = groupMask M r s r.T j := by
  exact ⟨lower_group_mask M d s i A B C d.D A _ hA hne hA Finset.Subset.rfl j hj,
    lower_group_mask M d s i A B C d.C B ∅ hA hne hB (empty_subset _) j hj,
    lower_group_mask M d s i A B C d.T C ∅ hA hne hC (empty_subset _) j hj⟩

lemma focal_incoming_path (M : Matroid (Fin n)) (hE : M.E = Set.univ) (κ : ℕ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) (hne : A.Nonempty) (k : ℤ) :
    let f := focalMasks d (trueGroup M d s i) A B C
    let r := focalReference M d s i
    guardedPath M hE κ (groupMask M f s f.D) (groupMask M f s f.C) (focalIndex M d s i) k =
      guardedPath M hE κ (groupMask M r s r.D) (groupMask M r s r.C) (focalIndex M d s i) k := by
  apply guardedPath_congr_prefix
  · exact fun j hj => (focal_prefix_masks M d s i A B C hA hB hC hne j hj).1
  · exact fun j hj => (focal_prefix_masks M d s i A B C hA hB hC hne j hj).2.1

lemma focal_lowerCompetition (M : Matroid (Fin n)) (hE : M.E = Set.univ) (κ : ℕ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) (hne : A.Nonempty) (k : ℤ) :
    let f := focalMasks d (trueGroup M d s i) A B C
    let r := focalReference M d s i
    lowerCompetition M hE κ (groupMask M f s f.D) (groupMask M f s f.C)
        (groupMask M f s f.T) k (focalIndex M d s i) =
      lowerCompetition M hE κ (groupMask M r s r.D) (groupMask M r s r.C)
        (groupMask M r s r.T) k (focalIndex M d s i) := by
  apply lowerCompetition_congr_prefix
  · exact fun j hj => (focal_prefix_masks M d s i A B C hA hB hC hne j hj).1
  · exact fun j hj => (focal_prefix_masks M d s i A B C hA hB hC hne j hj).2.1
  · exact fun j hj => (focal_prefix_masks M d s i A B C hA hB hC hne j hj).2.2

lemma focal_nominal_path (M : Matroid (Fin n)) (hE : M.E = Set.univ) (κ : ℕ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) (hne : A.Nonempty) (k : ℤ) :
    let f := focalMasks d (trueGroup M d s i) A B C
    let r := focalReference M d s i
    nominalPath M hE κ (groupMask M f s f.D) (groupMask M f s f.C) (focalIndex M d s i) k =
      densityEnabled M hE κ (A : Set (Fin n)) (activation (focalIndex M d s i)) k
        (guardedPath M hE κ (groupMask M r s r.D) (groupMask M r s r.C) (focalIndex M d s i) k) := by
  dsimp only
  rw [nominalPath, focal_incoming_path M hE κ d s i A B C hA hB hC hne k]
  congr 1
  exact focal_group_mask M d s i A B C d.D A hA hne hA

lemma focal_observed_inter (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i) :
    let f := focalMasks d (trueGroup M d s i) A B C
    (f.H ∪ f.D ∪ f.C) ∩ trueGroup M d s i = A ∪ B := by
  dsimp only [focalMasks]
  rw [Finset.union_inter_distrib_right, Finset.union_inter_distrib_right,
    disjoint_iff_inter_eq_empty.mp (trueGroup_disjoint_H M d s i).symm,
    replaceMask_inter_self _ _ _ hA, replaceMask_inter_self _ _ _ hB, Finset.empty_union]

lemma focal_listed_iff_nonempty (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) :
    i ∈ groups M (focalMasks d (trueGroup M d s i) A B C) s ↔ A.Nonempty := by
  rw [mem_groups, listed_focalMasks M d s i A B C hA]
  by_cases hne : A.Nonempty <;> simp [hne]

noncomputable def listedSafeStatistic (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (ε : Fin 2) : ℕ :=
  if i ∈ groups M d s then
    safeLayerStatistic M hE κ (groupMask M d s d.D) (groupMask M d s d.C)
      (groupMask M d s d.T) ((groups M d s).idxOf i) (trueGroup M d s i : Set (Fin n))
      ((d.D : Set (Fin n)) ∩ Y) ε
  else 0

noncomputable def listedRankStatistic (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (ε : Fin 2) : ℕ :=
  if i ∈ groups M d s then
    nominalRankStatistic M hE κ (groupMask M d s d.D) (groupMask M d s d.C)
      (groupMask M d s d.T) ((groups M d s).idxOf i) (trueGroup M d s i : Set (Fin n))
      ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) ε
  else 0

lemma listedSafeStatistic_focal_empty (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (B C : Finset (Fin n)) (Y : Set (Fin n)) (ε : Fin 2) :
    listedSafeStatistic M hE κ (focalMasks d (trueGroup M d s i) ∅ B C) s i Y ε = 0 := by
  rw [listedSafeStatistic, ite_eq_right]
  simp only [focal_listed_iff_nonempty M d s i ∅ B C (Finset.empty_subset _),
    Finset.not_nonempty_empty, not_false_eq_true]

lemma listedRankStatistic_focal_empty (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (B C : Finset (Fin n)) (ε : Fin 2) :
    listedRankStatistic M hE κ (focalMasks d (trueGroup M d s i) ∅ B C) s i ε = 0 := by
  rw [listedRankStatistic, ite_eq_right]
  simp only [focal_listed_iff_nonempty M d s i ∅ B C (Finset.empty_subset _),
    Finset.not_nonempty_empty, not_false_eq_true]

lemma listedSafeStatistic_focal_nonempty (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (A B C : Finset (Fin n)) (Y : Set (Fin n)) (ε : Fin 2)
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty) :
    let f := focalMasks d (trueGroup M d s i) A B C
    listedSafeStatistic M hE κ f s i Y ε =
      safeLayerStatistic M hE κ (groupMask M f s f.D) (groupMask M f s f.C)
        (groupMask M f s f.T) (focalIndex M d s i) (trueGroup M d s i : Set (Fin n))
        ((f.D : Set (Fin n)) ∩ Y) ε := by
  dsimp only
  rw [listedSafeStatistic, ite_eq_left ((focal_listed_iff_nonempty M d s i A B C hA).mpr hne),
    groups_focalMasks M d s i A B C hA hne, trueGroup_focalMasks]
  rfl

lemma listedRankStatistic_focal_nonempty (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (A B C : Finset (Fin n)) (ε : Fin 2)
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty) :
    let f := focalMasks d (trueGroup M d s i) A B C
    listedRankStatistic M hE κ f s i ε =
      nominalRankStatistic M hE κ (groupMask M f s f.D) (groupMask M f s f.C)
        (groupMask M f s f.T) (focalIndex M d s i) (trueGroup M d s i : Set (Fin n))
        ((f.H ∪ f.D ∪ f.C : Finset (Fin n)) : Set (Fin n)) ε := by
  dsimp only
  rw [listedRankStatistic, ite_eq_left ((focal_listed_iff_nonempty M d s i A B C hA).mpr hne),
    groups_focalMasks M d s i A B C hA hne, trueGroup_focalMasks]
  rfl

lemma focal_density_inter (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n))) :
    ((focalMasks d (trueGroup M d s i) A B C).D : Set (Fin n)) ∩ Y =
      (A : Set (Fin n)) ∩ Y := by
  ext e
  simp only [Set.mem_inter_iff, Finset.mem_coe, focalMasks, Finset.mem_union,
    Finset.mem_sdiff]
  constructor
  · rintro ⟨he | he, heY⟩
    · exact False.elim (he.2 (hY heY))
    · exact ⟨he, heY⟩
  · rintro ⟨heA, heY⟩
    exact ⟨Or.inr heA, heY⟩

end MainAlgorithm
end MatroidProphet

end OAI
