import OAI.Combinatorics.ContingencyTables.Dense.DenseCompletionTest

namespace OAI

/-! # Binary construction of the completed integer matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

def completedEntry (z : CompletionCell) : ℕ := (completionParts z).1-(completionParts z).2

def completedEntryRealizer : Realizer completedEntry :=
  composition (composition completionPartsRealizer (pair first second)) subtract

theorem polynomial_completedEntry : PolynomialTime completedEntryRealizer :=
  polynomial_composition (polynomial_composition polynomial_completionParts
    (polynomial_pair polynomial_first polynomial_second)) polynomial_subtract

def completionRows (z : CompletionData) : List ℕ := List.range z.1.1.length
def completionColumns (z : CompletionData) : List ℕ := List.range z.1.2.length

def completionRowsRealizer : Realizer completionRows :=
  composition (composition (composition first first) listLength) range
def completionColumnsRealizer : Realizer completionColumns :=
  composition (composition (composition first second) listLength) range

lemma polynomial_completionRows : PolynomialTime completionRowsRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_listLength) X
  intro z
  simp only [Function.comp_apply,eval_X]
  exact (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

lemma polynomial_completionColumns : PolynomialTime completionColumnsRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_listLength) X
  intro z
  simp only [Function.comp_apply,eval_X]
  exact (list_length_le_weight z.1.2).trans ((weight_snd z.1).trans (weight_fst z))

def completedRowEntry (z : (CompletionData×ℕ)×ℕ) : ℕ := completedEntry (z.1.1,(z.1.2,z.2))
def completedRowEntryRealizer : Realizer completedRowEntry :=
  composition (pair (composition first first) (pair (composition first second) second)) completedEntryRealizer

lemma polynomial_completedRowEntry : PolynomialTime completedRowEntryRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second))
    polynomial_completedEntry

def completedRow (z : CompletionData×ℕ) : List ℕ :=
  (completionColumns z.1).map (fun j => completedRowEntry (z,j))
def completedRowRealizer : Realizer completedRow :=
  composition (pair identity (composition first completionColumnsRealizer)) (mapWith completedRowEntryRealizer)

lemma polynomial_completedRow : PolynomialTime completedRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_completionColumns))
    (polynomial_mapWith polynomial_completedRowEntry)

def completedMatrix (z : CompletionData) : MatrixCode :=
  (completionRows z).map (fun i => completedRow (z,i))
def completedMatrixRealizer : Realizer completedMatrix :=
  composition (pair identity completionRowsRealizer) (mapWith completedRowRealizer)

theorem polynomial_completedMatrix : PolynomialTime completedMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_completionRows)
    (polynomial_mapWith polynomial_completedRow)

lemma completedEntry_code {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (z : Fin m → Fin n → ℕ) (i : Option (Fin m)) (j : Option (Fin n)) :
    completedEntry (((marginCode R,marginCode P),matrixCode z),(optionIndex i,optionIndex j))=
      DenseAffine.naturalTable R P (fun ij => z ij.1 ij.2) i j := by
  have h := completionParts_signed R P z i j
  unfold completedEntry DenseAffine.naturalTable
  dsimp only at h
  rw [←h]
  omega

lemma optionIndex_finSucc {m : ℕ} (i : Fin (m+1)) : optionIndex (finSuccEquiv m i)=i.val := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [finSuccEquiv_zero,optionIndex,Fin.val_zero]
  · simp only [finSuccEquiv_succ,optionIndex,Fin.val_succ]

private lemma completedRow_code {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (z : Fin m → Fin n → ℕ) (i : Fin (m+1)) :
    completedRow (((marginCode R,marginCode P),matrixCode z),i.val)=
      List.ofFn (fun j : Fin (n+1) => DenseAffine.naturalTable R P
        (fun ij => z ij.1 ij.2) (finSuccEquiv m i) (finSuccEquiv n j)) := by
  have hc : completionColumns ((marginCode R,marginCode P),matrixCode z)=List.range (n+1) := by
    simp only [completionColumns,marginCode,List.length_cons,List.length_ofFn]
  unfold completedRow
  rw [hc]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro j hj _
    have hjn : j < n+1 := by simpa only [List.length_map,List.length_range] using hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,completedRowEntry]
    simpa only [optionIndex_finSucc] using
      completedEntry_code R P z (finSuccEquiv m i) (finSuccEquiv n ⟨j,hjn⟩)

theorem completedMatrix_code {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (z : Fin m → Fin n → ℕ) :
    completedMatrix ((marginCode R,marginCode P),matrixCode z)=
      matrixCode (fun i : Fin (m+1) => fun j : Fin (n+1) =>
        DenseAffine.naturalTable R P (fun ij => z ij.1 ij.2) (finSuccEquiv m i) (finSuccEquiv n j)) := by
  have hr : completionRows ((marginCode R,marginCode P),matrixCode z)=List.range (m+1) := by
    simp only [completionRows,marginCode,List.length_cons,List.length_ofFn]
  unfold completedMatrix
  rw [hr]
  unfold matrixCode
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have him : i < m+1 := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact completedRow_code R P z ⟨i,him⟩

end ContingencyTables.DensePrograms

end OAI
