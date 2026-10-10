import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! The residual family is invariant under every change of the focal group's
three masks, including the unlisted outcome with empty density mask. -/

namespace MatroidProphet.FocalInvariance
open Finset MainAlgorithm
variable {n : ℕ}

lemma focalMasks_overwrite (d : MainMasks n) (U A B C A' B' C' : Finset (Fin n))
    (hA : A ⊆ U) (hB : B ⊆ U) (hC : C ⊆ U) :
    focalMasks (focalMasks d U A B C) U A' B' C' = focalMasks d U A' B' C' := by
  have hD : ((d.D \ U) ∪ A) \ U = d.D \ U := by
    ext e
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨he | he, hn⟩
      · exact he
      · exact False.elim (hn (hA he))
    · intro he
      exact ⟨Or.inl he, he.2⟩
  have hG : ((d.C \ U) ∪ B) \ U = d.C \ U := by
    ext e
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨he | he, hn⟩
      · exact he
      · exact False.elim (hn (hB he))
    · intro he
      exact ⟨Or.inl he, he.2⟩
  have hT : ((d.T \ U) ∪ C) \ U = d.T \ U := by
    ext e
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨he | he, hn⟩
      · exact he
      · exact False.elim (hn (hC he))
    · intro he
      exact ⟨Or.inl he, he.2⟩
  simp only [focalMasks, hD, hG, hT]

lemma focalReference_focalMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) :
    focalReference M (focalMasks d (trueGroup M d s i) A B C) s i =
      focalReference M d s i := by
  unfold focalReference
  rw [trueGroup_focalMasks]
  exact focalMasks_overwrite d _ A B C _ ∅ ∅ hA hB hC

lemma focalIndex_focalMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) :
    focalIndex M (focalMasks d (trueGroup M d s i) A B C) s i = focalIndex M d s i := by
  unfold focalIndex
  rw [focalReference_focalMasks M d s i A B C hA hB hC]

/-- Equality before conditioning on listing: the fixed family uses only H,
parity, weights, and density/guard/test bits outside the true group. -/
lemma focalResidualFamily_focalMasks (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (ε : Fin 2)
    (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) :
    focalResidualFamily M hE κ (focalMasks d (trueGroup M d s i) A B C) s i ε =
      focalResidualFamily M hE κ d s i ε := by
  let family := fun (r : MainMasks n) (h : ℕ) (U : Finset (Fin n)) =>
    labeledResidualFamily M U κ
      (guardedPath M hE κ (groupMask M r s r.D) (groupMask M r s r.C) h)
      (activation h) ε (fun b => lowerCompetition M hE κ
        (groupMask M r s r.D) (groupMask M r s r.C) (groupMask M r s r.T) b.val.val h)
  change family (focalReference M (focalMasks d (trueGroup M d s i) A B C) s i)
      (focalIndex M (focalMasks d (trueGroup M d s i) A B C) s i)
      (trueGroup M (focalMasks d (trueGroup M d s i) A B C) s i) =
    family (focalReference M d s i) (focalIndex M d s i) (trueGroup M d s i)
  rw [focalReference_focalMasks M d s i A B C hA hB hC,
    focalIndex_focalMasks M d s i A B C hA hB hC, trueGroup_focalMasks]

end MatroidProphet.FocalInvariance

end OAI
