import OAI.Combinatorics.ContingencyTables.Dense.DenseIntegerTable
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileExchangeProgram
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialSums

namespace OAI

/-! # Binary list arithmetic for integral dense completion -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators

abbrev MatrixCode := List (List ℕ)

def columnRead (z : ℕ×List ℕ) : ℕ := z.2.getD z.1 0

def columnReadRealizer : Realizer columnRead :=
  composition (pair second first) (getDFast 0)

lemma polynomial_columnRead : PolynomialTime columnReadRealizer :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_first) (polynomial_getDFast 0)

def columnTotal (z : MatrixCode×ℕ) : ℕ := (z.1.map (fun row => row.getD z.2 0)).sum

def columnTotalRealizer : Realizer columnTotal :=
  composition (composition (pair second first) (mapWith columnReadRealizer)) listSum

theorem polynomial_columnTotal : PolynomialTime columnTotalRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_second polynomial_first)
    (polynomial_mapWith polynomial_columnRead)) polynomial_listSum

def rowTotal (z : MatrixCode×ℕ) : ℕ := (z.1.getD z.2 []).sum

def rowTotalRealizer : Realizer rowTotal := composition (getDFast []) listSum

theorem polynomial_rowTotal : PolynomialTime rowTotalRealizer :=
  polynomial_composition (polynomial_getDFast []) polynomial_listSum

def matrixTotal (z : MatrixCode) : ℕ := (z.map List.sum).sum

def matrixTotalRealizer : Realizer matrixTotal := composition (map listSum) listSum

theorem polynomial_matrixTotal : PolynomialTime matrixTotalRealizer :=
  polynomial_composition (polynomial_map polynomial_listSum) polynomial_listSum

def matrixEntry (z : MatrixCode×(ℕ×ℕ)) : ℕ := (z.1.getD z.2.1 []).getD z.2.2 0

def matrixEntryRealizer : Realizer matrixEntry :=
  composition (pair (composition (pair first (composition second first)) (getDFast []))
    (composition second second)) (getDFast 0)

theorem polynomial_matrixEntry : PolynomialTime matrixEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast []))
    (polynomial_composition polynomial_second polynomial_second)) (polynomial_getDFast 0)

def matrixCode {m n : ℕ} (z : Fin m → Fin n → ℕ) : MatrixCode :=
  List.ofFn (fun i => List.ofFn (z i))

lemma matrixEntry_code {m n : ℕ} (z : Fin m → Fin n → ℕ) (i : Fin m) (j : Fin n) :
    matrixEntry (matrixCode z,(i.val,j.val))=z i j := by
  simp only [matrixEntry,matrixCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,j.isLt,dite_true,Option.getD_some,Fin.eta]

lemma rowTotal_code {m n : ℕ} (z : Fin m → Fin n → ℕ) (i : Fin m) :
    rowTotal (matrixCode z,i.val)=∑ j,z i j := by
  simp only [rowTotal,matrixCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,dite_true,Option.getD_some,Fin.eta,List.sum_ofFn]

lemma columnTotal_code {m n : ℕ} (z : Fin m → Fin n → ℕ) (j : Fin n) :
    columnTotal (matrixCode z,j.val)=∑ i,z i j := by
  simp only [columnTotal,matrixCode,List.map_ofFn,Function.comp_apply,List.getD_eq_getElem?_getD,
    List.getElem?_ofFn,j.isLt,dite_true,Option.getD_some,Fin.eta,List.sum_ofFn]

lemma matrixTotal_code {m n : ℕ} (z : Fin m → Fin n → ℕ) :
    matrixTotal (matrixCode z)=∑ i,∑ j,z i j := by
  simp only [matrixTotal,matrixCode,List.map_ofFn,Function.comp_apply,List.sum_ofFn]

end ContingencyTables.DensePrograms

end OAI
