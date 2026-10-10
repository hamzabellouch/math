import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialMatrixFold

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
abbrev addMatrices (A B : MatrixData) := zipDefault (zipDefault (fun z : ℚ×ℚ => z.1+z.2) 0 0) [] [] (A,B)
lemma matrixAdd_shape {L : ℕ} (A B : MatrixData) (h : MatrixShape L A) :
    MatrixShape L (addMatrices A B) := by
  constructor
  · simpa only [addMatrices,zipDefault,List.length_map,List.length_range] using h.1
  · intro row hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    simp only [zipDefault,List.length_map,List.length_range]
    exact getD_property (fun row : List ℚ => row.length≤L) A [] i (by simp) h.2
lemma matrixAdd_parts {H K : ℕ} (A B : MatrixData) (ha : MatrixParts H A) (hb : MatrixParts K B) :
    MatrixParts (H+K+1) (addMatrices A B) := by
  apply zipDefault_property (fun row => ∀q∈row,QParts H q) (fun row => ∀q∈row,QParts K q)
    (fun row => ∀q∈row,QParts (H+K+1) q) _ [] [] A B (by simp) (by simp) ha hb
  intro x y hx hy
  exact zipDefault_property _ _ _ _ 0 0 x y (qparts_zero _) (qparts_zero _) hx hy (fun a b ha hb => ha.add hb)
lemma matrixAdd_fold {L H : ℕ} (A : MatrixData) (xs : List MatrixData)
    (shape : MatrixShape L A) (parts : MatrixParts H A) (hp : ∀p∈xs,MatrixParts L p) :
    MatrixShape L (xs.foldl addMatrices A) ∧ MatrixParts (H+xs.length*(L+1)) (xs.foldl addMatrices A) := by
  induction xs generalizing A H with
  | nil => simpa using And.intro shape parts
  | cons x xs ih =>
    have h := ih (addMatrices A x) (matrixAdd_shape A x shape)
      (matrixAdd_parts A x parts (hp x (by simp))) (fun p hp' => hp p (by simp [hp']))
    simpa only [List.foldl_cons,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h
instance size_matrixAdd : FoldSize matrixAdd := by
  refine ⟨⟨1000*(X+1)^4,?_⟩⟩
  intro A xs ys zs h
  let L := (prodCode matrixCode (listCode matrixCode) (A,xs)).length
  have ha : (matrixCode A).length≤L := le_prodCode_left (A,xs)
  have hy : (listCode matrixCode ys).length≤L :=
    (prefix_code_length _ xs ys zs h).trans (le_prodCode_right (A,xs))
  have hn := (list_length_le_code _ _).trans hy
  have ht := matrixAdd_fold A ys ((matrixShape_length A).mono ha) ((matrixParts_length A).mono ha)
    (fun p hp => (matrixParts_length p).mono ((mem_length_le_code ys hp).trans hy))
  have he := matrix_length_bound ht.2 ht.1
  apply he.trans
  change L*(2*(L*(2*(4*(L+ys.length*(L+1))+7)+1))+1)≤1000*(L+1)^4
  calc
    _≤L*(2*(L*(2*(4*(L+L*(L+1))+7)+1))+1) := by gcongr
    _≤_ := by nlinarith [Nat.zero_le L, sq_nonneg (L:ℤ)]
end CurrentKS.Realization

end

end OAI
