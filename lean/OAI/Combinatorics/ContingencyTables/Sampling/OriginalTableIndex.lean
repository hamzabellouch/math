import OAI.Combinatorics.ContingencyTables.Sampling.OriginalTableBox
import OAI.Combinatorics.ContingencyTables.Dense.GridIndexProgram

namespace OAI

/-! # Binary lookup of an original table's finite-box index -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

def originalIndexInput (z : CompletionMargins×MatrixCode) : GridIndexData :=
  (z.2.flatten,z.1.1.sum+1)

def originalIndexInputRealizer : Realizer originalIndexInput :=
  pair (composition second flatten)
    (composition (composition (composition first first) listSum) successor)

lemma polynomial_originalIndexInput : PolynomialTime originalIndexInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_flatten)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_listSum) polynomial_successor)

def originalIndex (z : CompletionMargins×MatrixCode) : ℕ := gridIndex (originalIndexInput z)

def originalIndexRealizer : Realizer originalIndex :=
  composition originalIndexInputRealizer gridIndexRealizer

lemma polynomial_originalIndex : PolynomialTime originalIndexRealizer :=
  polynomial_composition polynomial_originalIndexInput polynomial_gridIndex

lemma matrixCode_flatten {m n : ℕ} (X : Fin m → Fin n → ℕ) :
    (matrixCode X).flatten=List.ofFn (fun k : Fin (m*n) =>
      X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  let k : Fin (m*n) := ⟨i.val*n+j.val,by nlinarith [i.isLt,j.isLt]⟩
  have hk : finProdFinEquiv (i,j)=k := Fin.ext (by dsimp [k,finProdFinEquiv]; ac_rfl)
  change X i j=X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  rw [←hk,Equiv.symm_apply_apply]

lemma originalIndex_actual {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (T : Table r c) :
    originalIndex ((List.ofFn r,List.ofFn c),matrixCode T.val)=
      (OriginalTableBox.index r c le_rfl T).val := by
  unfold originalIndex originalIndexInput
  rw [matrixCode_flatten,List.sum_ofFn]
  change gridIndex (List.ofFn (fun k =>
    (OriginalTableBox.encode r c le_rfl T k).val),(∑ i,r i)+1)=_
  rw [gridIndex_ofFn]
  rfl

end ContingencyTables.ProfilePrograms

end OAI
