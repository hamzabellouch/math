import OAI.Combinatorics.ContingencyTables.Sampling.OriginalTableEnumeration
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileBoxEnumeration
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperCorrectionBudget
import OAI.Combinatorics.ContingencyTables.Sampling.RareBranchRuntime

namespace OAI

/-! # The boxes actually enumerated by the exact correction have singly exponential size -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts SmallContextCoordinates
open PhysicalCompletionFibres FirstPaperPhysicalMarginal
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c

lemma originalEnumeration_count :
    gridStateCount (originalEnumerationData (List.ofFn r,List.ofFn c))=((∑ i,r i)+1)^(m*n) := by
  rw [gridStateCount_eq]
  simp only [originalEnumerationData,originalLayoutMargins,completionEnumerationData,
    zeroGrid,List.tail_cons,cellPairs,List.length_map,List.length_range,List.length_ofFn,
    List.sum_cons,List.sum_ofFn,zero_add]

lemma originalEnumeration_count_bound :
    gridStateCount (originalEnumerationData (List.ofFn r,List.ofFn c))≤2^(d*b) := by
  rw [originalEnumeration_count]
  have hN : (∑ i,r i)+1≤2^b :=
    (show (∑ i,r i)+1≤ stateBound r c+1 by unfold stateBound; omega).trans
      (smallBinaryLength_parameters r c).2.2
  have hdim : m*n≤d := by unfold dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  calc
    ((∑ i,r i)+1)^(m*n) ≤ (2^b)^(m*n) := Nat.pow_le_pow_left hN _
    _ = 2^(b*(m*n)) := (pow_mul _ _ _).symm
    _ ≤ 2^(d*b) := Nat.pow_le_pow_right (by decide) (by nlinarith)

lemma profileEnumeration_count (e : Fin q ≃ Cells (paperSmall r c)) (x : PaperStates r c) :
    gridStateCount (profileEnumerationData (stateCodeData r c e x))=(d^20+1)^(q+q) := by
  rw [gridStateCount_eq]
  simp only [profileEnumerationData,stateCodeData,codeCheckData,cellCatalog,List.length_map,
    List.length_append,List.length_ofFn]

lemma profileEnumeration_count_bound (e : Fin q ≃ Cells (paperSmall r c)) (x : PaperStates r c) :
    gridStateCount (profileEnumerationData (stateCodeData r c e x))≤2^(2*(d*b)) := by
  rw [profileEnumeration_count]
  have hU : d^20+1≤2^b :=
    (show d^20+1≤ stateBound r c+1 by unfold stateBound; omega).trans
      (smallBinaryLength_parameters r c).2.2
  have hq : q≤d := by
    have he : q=Fintype.card (Cells (paperSmall r c)) := by
      simpa only [Fintype.card_fin] using Fintype.card_congr e
    rw [he]
    exact (RowMajorEnumeration.small_card_le_dimension (paperSmall r c)).trans dimension_le_allowance
  calc
    (d^20+1)^(q+q) ≤ (2^b)^(q+q) := Nat.pow_le_pow_left hU _
    _ = 2^(b*(q+q)) := (pow_mul _ _ _).symm
    _ ≤ 2^(2*(d*b)) := Nat.pow_le_pow_right (by decide) (by nlinarith)

/-- Any fixed polynomial of the product of these enumeration sizes is
absorbed by the actual correction probability. -/
lemma exact_boxes_absorbed (p : Polynomial ℕ) (A : ℕ) :
    p.eval (A*2^(3*(d*b)))≤2^(correctionPrecision r c)*
      (p.eval A*2^((3*p.natDegree)^2)) := by
  apply RareBranchRuntime.polynomial_tabulation_bound
  exact RareBranchRuntime.square_le_precision d b (by unfold dimensionAllowance; omega)

end
end ContingencyTables.SmallGraphProfiles

end OAI
