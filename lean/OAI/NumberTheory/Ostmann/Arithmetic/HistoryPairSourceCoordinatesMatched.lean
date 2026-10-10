import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesMatching
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceCoordinatesBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSourceCoordinates
open Construction HistoryOccurrenceVariables HistoryPairPattern HistoryPairRows
open HistoryPairRepresentatives HistoryPairRepresentativeVariables HistoryPairBulkCoordinates
open HistoryRepeatedRenaming
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem sourceMap_surjective_of_matching (h k : History l) (e : RootMatching h k) :
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
    · exact ⟨.inr (.inl (e.positions i)),(e.key_eq i).symm⟩
    · exact ⟨.inr (.inr (label h k (.inr i))),rfl⟩

def sourceEquivMatched (h k : History l) (hs : h.Supported V outside)
    (e : RootMatching h k) : Coordinates h k ≃ PairKey h k :=
  Equiv.ofBijective (sourceMap h k)
    ⟨sourceMap_injective h k hs,sourceMap_surjective_of_matching h k e⟩

@[simp] theorem sourceEquivMatched_apply (h k : History l) (hs : h.Supported V outside)
    (e : RootMatching h k) (i : Coordinates h k) :
    sourceEquivMatched h k hs e i = sourceMap h k i := rfl

@[simp] theorem sourceEquivMatched_sample (h k : History l) (hs : h.Supported V outside)
    (e : RootMatching h k) (i : Coordinates h k) :
    pairSample h k (sourceEquivMatched h k hs e i) = coordinateSample h k i :=
  sourceMap_sample h k i

@[simp] theorem sourceEquivMatched_symm_sample (h k : History l) (hs : h.Supported V outside)
    (e : RootMatching h k) (q : PairKey h k) :
    coordinateSample h k ((sourceEquivMatched h k hs e).symm q) = pairSample h k q := by
  rw [←sourceEquivMatched_sample h k hs e,Equiv.apply_symm_apply]

theorem sourceEquivMatched_symm_right_sample (h k : History l) (hs : h.Supported V outside)
    (e : RootMatching h k) (hg : RootGiantsAgree h k) (i : Key k) :
    coordinateSample h k ((sourceEquivMatched h k hs e).symm (rightMap h k i)) =
      integerSample k i := by
  rw [sourceEquivMatched_symm_sample,rightMap_sample h k hg]

theorem sourceEquivMatched_eq (h k : History l) (hs : h.Supported V outside)
    (e e' : RootMatching h k) : sourceEquivMatched h k hs e = sourceEquivMatched h k hs e' := by
  ext i
  rfl

def blockSourceEquivMatched (h k : History l) (hs : h.Supported V outside)
    (e : RootMatching h k) {β : Type*} (b : Representative h k ≃ β) :
    (Bool ⊕ (Fin h.root.small.length ⊕ β)) ≃ PairKey h k :=
  (Equiv.sumCongr (Equiv.refl Bool)
    (Equiv.sumCongr (Equiv.refl _) b.symm)).trans (sourceEquivMatched h k hs e)

@[simp] theorem blockSourceEquivMatched_giant (h k : History l) (hs : h.Supported V outside)
    (e : RootMatching h k) {β : Type*} (b : Representative h k ≃ β) (t : Bool) :
    blockSourceEquivMatched h k hs e b (.inl t) = leftMap h k (.inl t) := rfl

@[simp] theorem blockSourceEquivMatched_root (h k : History l) (hs : h.Supported V outside)
    (e : RootMatching h k) {β : Type*} (b : Representative h k ≃ β)
    (i : Fin h.root.small.length) :
    blockSourceEquivMatched h k hs e b (.inr (.inl i)) = rootKey h k i := rfl

@[simp] theorem blockSourceEquivMatched_block (h k : History l) (hs : h.Supported V outside)
    (e : RootMatching h k) {β : Type*} (b : Representative h k ≃ β) (q : β) :
    blockSourceEquivMatched h k hs e b (.inr (.inr q)) = representativeMap h k (b.symm q) := rfl

end Ostmann.Arithmetic.HistoryPairSourceCoordinates

end

end OAI
