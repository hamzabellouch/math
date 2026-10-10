import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairRepresentativeVariables

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSourceCoordinates
open Construction HistoryOccurrenceVariables HistoryPairPattern HistoryPairRows
open HistoryPairRepresentatives HistoryPairRepresentativeVariables HistoryPairBulkCoordinates
open HistoryRepeatedRenaming
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

abbrev Coordinates (h k : History l) :=
  Bool ⊕ (Fin h.root.small.length ⊕ Representative h k)

def sourceMap (h k : History l) : Coordinates h k → PairKey h k :=
  Sum.elim (fun b => leftMap h k (.inl b))
    (Sum.elim (rootKey h k) (representativeMap h k))

@[simp] theorem representativeMap_left_label (h k : History l) (i : InternalKey h) :
    representativeMap h k (label h k (.inl i)) = leftMap h k (.inr (.inr i)) := rfl

@[simp] theorem representativeMap_right_label (h k : History l) (i : InternalKey k) :
    representativeMap h k (label h k (.inr i)) = rightMap h k (.inr (.inr i)) := rfl

theorem representative_level_le (h k : History l) (r : Representative h k) : r.val.1 ≤ l := by
  obtain ⟨i,rfl⟩ := label_surjective h k r
  rcases i with i | i
  · exact (internalLevel_pos_le h i).2
  · exact (internalLevel_pos_le k i).2

theorem rootKey_ne_representativeMap (h k : History l)
    (i : Fin h.root.small.length) (r : Representative h k) :
    rootKey h k i ≠ representativeMap h k r := by
  intro he
  have hh := congrArg (pairLevel h k) he
  have hl := representative_level_le h k r
  change l+1 = r.val.1 at hh
  omega

theorem sourceMap_injective (h k : History l) (hs : h.Supported V outside) :
    Function.Injective (sourceMap h k) := by
  intro a b he
  rcases a with a | a | a <;> rcases b with b | b | b
  · have hv := congrArg Subtype.val he
    exact congrArg Sum.inl (Sum.inl.inj hv)
  · have hv := congrArg Subtype.val he
    cases hv
  · have hv := congrArg Subtype.val he
    cases hv
  · have hv := congrArg Subtype.val he
    cases hv
  · exact congrArg (fun i => Sum.inr (Sum.inl i)) (rootKey_injective h k hs he)
  · exact False.elim (rootKey_ne_representativeMap h k a b he)
  · have hv := congrArg Subtype.val he
    cases hv
  · exact False.elim (rootKey_ne_representativeMap h k b a he.symm)
  · exact congrArg (fun r => Sum.inr (Sum.inr r)) (representativeMap_injective h k he)

theorem right_root_in_range (h k : History l) (hperm : h.root.small.Perm k.root.small)
    (i : Fin k.root.small.length) :
    ∃ j : Fin h.root.small.length, rootKey h k j = rightMap h k (.inr (.inl i)) := by
  have hm := hperm.mem_iff.mpr (List.get_mem k.root.small i)
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hm
  refine ⟨j,Subtype.ext ?_⟩
  change Sum.inr (l+1,((h.root.small.get j).value:ℤ)) =
    (Sum.inr (l+1,((k.root.small.get i).value:ℤ)) : Bool ⊕ (ℕ × ℤ))
  rw [hj]

theorem sourceMap_surjective (h k : History l) (hperm : h.root.small.Perm k.root.small) :
    Function.Surjective (sourceMap h k) := by
  intro q
  obtain ⟨i,rfl⟩ := unionMap_surjective h k q
  rcases i with i | i
  · rcases i with b | i | i
    · exact ⟨.inl b,rfl⟩
    · exact ⟨.inr (.inl i),rfl⟩
    · exact ⟨.inr (.inr (label h k (.inl i))),rfl⟩
  · rcases i with b | i | i
    · exact ⟨.inl b,rfl⟩
    · obtain ⟨j,hj⟩ := right_root_in_range h k hperm i
      exact ⟨.inr (.inl j),hj⟩
    · exact ⟨.inr (.inr (label h k (.inr i))),rfl⟩

def sourceEquiv (h k : History l) (hs : h.Supported V outside)
    (hperm : h.root.small.Perm k.root.small) : Coordinates h k ≃ PairKey h k :=
  Equiv.ofBijective (sourceMap h k)
    ⟨sourceMap_injective h k hs,sourceMap_surjective h k hperm⟩

@[simp] theorem sourceEquiv_apply (h k : History l) (hs : h.Supported V outside)
    (hperm : h.root.small.Perm k.root.small) (i : Coordinates h k) :
    sourceEquiv h k hs hperm i = sourceMap h k i := rfl

def coordinateSample (h k : History l) : Coordinates h k → ℤ :=
  Sum.elim (fun b => integerSample h (.inl b))
    (Sum.elim (fun i => (h.root.small.get i).value) (fun r => prime h k r))

@[simp] theorem sourceMap_sample (h k : History l) (i : Coordinates h k) :
    pairSample h k (sourceMap h k i) = coordinateSample h k i := by
  rcases i with b | i | r
  · exact leftMap_sample h k (.inl b)
  · exact leftMap_sample h k (.inr (.inl i))
  · exact representativeMap_sample h k r

@[simp] theorem sourceEquiv_sample (h k : History l) (hs : h.Supported V outside)
    (hperm : h.root.small.Perm k.root.small) (i : Coordinates h k) :
    pairSample h k (sourceEquiv h k hs hperm i) = coordinateSample h k i :=
  sourceMap_sample h k i

@[simp] theorem sourceEquiv_symm_sample (h k : History l) (hs : h.Supported V outside)
    (hperm : h.root.small.Perm k.root.small) (q : PairKey h k) :
    coordinateSample h k ((sourceEquiv h k hs hperm).symm q) = pairSample h k q := by
  rw [← sourceEquiv_sample h k hs hperm, Equiv.apply_symm_apply]

theorem sourceEquiv_symm_right_sample (h k : History l) (hs : h.Supported V outside)
    (hperm : h.root.small.Perm k.root.small) (hg : RootGiantsAgree h k) (i : Key k) :
    coordinateSample h k ((sourceEquiv h k hs hperm).symm (rightMap h k i)) =
      integerSample k i := by
  rw [sourceEquiv_symm_sample,rightMap_sample h k hg]

end Ostmann.Arithmetic.HistoryPairSourceCoordinates

end

end OAI
