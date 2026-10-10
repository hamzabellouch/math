import OAI.Probability.SwitchChain.PairArrayEncoding

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.DisjointBlock
variable {O : Type*} [Fintype O]

 theorem first_sum_eq (U : Fin 2 → O → Bool) :
    (∑ o, (U 0 o).toNat) = (doubleSet (pairCount U)).card + (assignmentSet U).card := by
  have h := outsideArray_first_sum (pairCount U) (assignmentSet U)
    (assignmentSet_subset U)
  rwa [outsideArray_encode] at h

def arrayEquivSlice (c : O → ℕ) (hc : ∀ o, c o ≤ 2) (k : ℕ) :
    {U : Fin 2 → O → Bool // (∀ o, pairCount U o = c o) ∧
      (∑ o, (U 0 o).toNat) = (doubleSet c).card + k} ≃
    {A : Finset O // A ⊆ singleSet c ∧ A.card = k} where
  toFun U := ⟨assignmentSet U.val, by
    have hc' : pairCount U.val = c := funext U.property.1
    constructor
    · simpa only [singleSet, hc'] using assignmentSet_subset U.val
    · have h := first_sum_eq U.val
      rw [hc', U.property.2] at h
      omega⟩
  invFun A := ⟨outsideArray c A.val, by
    constructor
    · exact pairCount_outsideArray c hc A.val A.property.1
    · rw [outsideArray_first_sum c A.val A.property.1, A.property.2]⟩
  left_inv U := by
    apply Subtype.ext
    have hc' : pairCount U.val = c := funext U.property.1
    change outsideArray c (assignmentSet U.val) = U.val
    simpa only [hc'] using outsideArray_encode U.val
  right_inv A := by
    apply Subtype.ext
    exact assignmentSet_outsideArray c hc A.val A.property.1

 theorem card_assignmentSlice (c : O → ℕ) (k : ℕ) :
    Nat.card {A : Finset O // A ⊆ singleSet c ∧ A.card = k} =
      Nat.choose (singleSet c).card k := by
  classical
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_of_subtype ((singleSet c).powersetCard k)
    (fun A => Finset.mem_powersetCard)]
  exact Finset.card_powersetCard k (singleSet c)

 theorem card_arraySlice (c : O → ℕ) (hc : ∀ o, c o ≤ 2) (k : ℕ) :
    Nat.card {U : Fin 2 → O → Bool // (∀ o, pairCount U o = c o) ∧
      (∑ o, (U 0 o).toNat) = (doubleSet c).card + k} =
      Nat.choose (singleSet c).card k := by
  rw [Nat.card_congr (arrayEquivSlice c hc k)]
  exact card_assignmentSlice c k

end Problem315.DisjointBlock

end

end OAI
