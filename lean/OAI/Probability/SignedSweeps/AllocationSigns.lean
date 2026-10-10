import OAI.Probability.SignedSweeps.SignedPair

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) allocationSignsFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) allocationSignsSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma complexEquivSign_permCongr {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (g : Equiv.Perm A) :
    complexEquivSign (e.permCongr g) = complexEquivSign g := by
  simp only [complexEquivSign, equivSign_perm, Equiv.Perm.sign_permCongr]

def allocationBlockPermutation {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p)
    (a : SymmetricGroup u) (b : SymmetricGroup v) : SymmetricGroup p :=
  (allocationEquiv h S).permCongr (a.sumCongr b)

lemma allocationBlockPermutation_left {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p)
    (a : SymmetricGroup u) (b : SymmetricGroup v) (i : Fin u) :
    allocationBlockPermutation h S a b (allocationEquiv h S (Sum.inl i)) =
      allocationEquiv h S (Sum.inl (a i)) := by
  simp [allocationBlockPermutation, Equiv.permCongr_apply]

lemma allocationBlockPermutation_right {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p)
    (a : SymmetricGroup u) (b : SymmetricGroup v) (i : Fin v) :
    allocationBlockPermutation h S a b (allocationEquiv h S (Sum.inr i)) =
      allocationEquiv h S (Sum.inr (b i)) := by
  simp [allocationBlockPermutation, Equiv.permCongr_apply]

lemma allocationBlockPermutation_mem {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p)
    (a : SymmetricGroup u) (b : SymmetricGroup v) (i : Fin p) :
    i ∈ S.1 ↔ allocationBlockPermutation h S a b i ∈ S.1 := by
  obtain ⟨i,rfl⟩ := (allocationEquiv h S).surjective i
  cases i with
  | inl i => simp only [allocationBlockPermutation_left, allocationEquiv_left_mem]
  | inr i => simp only [allocationBlockPermutation_right, allocationEquiv_right_not_mem]

def allocationOddIndex {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p) :
    Fin v ≃ {i : Fin p // i ∉ S.1} :=
  (Fintype.equivFinOfCardEq (allocation_complement_card h S)).symm

lemma allocationOddIndex_val {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p) (i : Fin v) :
    (allocationOddIndex h S i).1 = allocationEquiv h S (Sum.inr i) := rfl

lemma allocation_odd_permutation {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p)
    (a : SymmetricGroup u) (b : SymmetricGroup v) :
    oddPositionSetEquiv (allocationBlockPermutation h S a b) S.1 S.1
        (allocationBlockPermutation_mem h S a b) =
      (allocationOddIndex h S).permCongr b := by
  apply Equiv.ext
  intro i
  obtain ⟨i,rfl⟩ := (allocationOddIndex h S).surjective i
  apply Subtype.ext
  change allocationBlockPermutation h S a b (allocationOddIndex h S i).1 = _
  rw [allocationOddIndex_val, allocationBlockPermutation_right]
  simp [Equiv.permCongr_apply, allocationOddIndex_val]

lemma wordPhase_allocation_internal {u v p : ℕ} {C : Type*} (h : u+v=p)
    (S : EvenAllocation u p) (a : SymmetricGroup u) (b : SymmetricGroup v)
    (w : Fin p → C ⊕ C) (hw : wordEvenSites w = S.1) :
    wordPhase (allocationBlockPermutation h S a b) w = complexSign v b := by
  have ht : wordEvenSites (w ∘ allocationBlockPermutation h S a b) = S.1 := by
    ext i
    rw [wordEvenSites_comp_mem, hw, ← allocationBlockPermutation_mem]
  calc
    _ = complexEquivSign (oddPositionSetEquiv (allocationBlockPermutation h S a b)
        S.1 S.1 (allocationBlockPermutation_mem h S a b)) :=
      oddPositionSetEquiv_sign_congr _ hw ht _ _
    _ = _ := by rw [allocation_odd_permutation, complexEquivSign_permCongr, complexEquivSign_perm]

lemma wordPhaseDiagonal_allocation {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (S : EvenAllocation u p) (a : SymmetricGroup u) (b : SymmetricGroup v) :
    wordPhaseDiagonal (allocationBlockPermutation h S a b) ∘ₗ
        (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap =
      complexSign v b • (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro w
  change wordPhase (allocationBlockPermutation h S a b) w *
    pairWordEmbedding (allocationEquiv h S) x w =
      complexSign v b * pairWordEmbedding (allocationEquiv h S) x w
  by_cases hw : wordEvenSites w = S.1
  · rw [wordPhase_allocation_internal h S a b w hw]
  · rw [pairWordEmbedding_off h S x w hw, mul_zero, mul_zero]

theorem pairWordEmbedding_signed_internal {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (S : EvenAllocation u p) (a : SymmetricGroup u) (b : SymmetricGroup v) :
    signedWordRepresentation p C (allocationBlockPermutation h S a b) ∘ₗ
        (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap =
      complexSign v b • ((pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap ∘ₗ
        TensorProduct.map (wordRepresentation u C a) (wordRepresentation v C b)) := by
  have he : (allocationEquiv h S).trans (allocationBlockPermutation h S a b) =
      (a.sumCongr b).trans (allocationEquiv h S) := by
    apply Equiv.ext
    intro i
    simp [allocationBlockPermutation, Equiv.permCongr_apply]
  change (wordPhaseDiagonal _ ∘ₗ wordRepresentation p (C ⊕ C) _) ∘ₗ _ = _
  rw [LinearMap.comp_assoc, pairWordEmbedding_reindex, he, pairWordEmbedding_internal,
    ← LinearMap.comp_assoc, wordPhaseDiagonal_allocation, LinearMap.smul_comp]

end SignedSweeps
end

end OAI
