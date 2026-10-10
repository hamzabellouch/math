import OAI.Combinatorics.ContingencyTables.Dense.DenseOffsetProgram

namespace OAI

/-! # The binary offset program computes the geometric free matrix -/

namespace ContingencyTables.DensePrograms
open GridBoundary ProfilePrograms
open scoped Classical

noncomputable section
variable {m n q K : ℕ}

lemma gridCellWidth_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (a : Grid (I := Fin q) K) (e : Fin m×Fin n ≃ Fin q)
    (i : Fin m) (j : Fin n) :
    gridCellWidth (exponentDataCode R P d
      (fun i j => (corner a (e (i,j))).toNat),(i.val,j.val))=
      integerWidth R P d (i,j) := by
  have hR := marginCode_getD R (some i)
  have hP := marginCode_getD P (some j)
  change (marginCode R).getD (i.val+1) 0=R (some i) at hR
  change (marginCode P).getD (j.val+1) 0=P (some j) at hP
  simp only [gridCellWidth,shiftedCell,exponentCellData,exponentDataCode,hR,hP,integerWidth]

lemma offsetBits_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (z : Fin m → Fin n → ℕ) (words : Fin (m*n) → List Bool)
    (i : Fin m) (j : Fin n) :
    offsetBits ((exponentDataCode R P d z,List.ofFn words),(i.val,j.val))=
      words (finProdFinEquiv (i,j)) := by
  have hv : i.val*n+j.val=(finProdFinEquiv (i,j)).val := by
    change i.val*n+j.val=j.val+n*i.val
    ac_rfl
  simp only [offsetBits,exponentDataCode,marginCode,List.tail_cons,List.length_ofFn,hv]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,(finProdFinEquiv (i,j)).isLt,
    dite_true,Option.getD_some,Fin.eta]

lemma offsetFreeEntry_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (a : Grid (I := Fin (m*n)) K) (words : Fin (m*n) → List Bool)
    (i : Fin m) (j : Fin n) :
    offsetFreeEntry ((exponentDataCode R P d
      (fun i j => (corner a (finProdFinEquiv (i,j))).toNat),List.ofFn words),(i.val,j.val))=
      cornerFree R P d finProdFinEquiv a (i,j)+
        scaledWordValue (integerWidth R P d (i,j),words (finProdFinEquiv (i,j))) := by
  simp only [offsetFreeEntry,gridCellValue_code,gridCellWidth_code,offsetBits_code]

private lemma offsetRow_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (a : Grid (I := Fin (m*n)) K) (words : Fin (m*n) → List Bool) (i : Fin m) :
    offsetRow ((exponentDataCode R P d
      (fun i j => (corner a (finProdFinEquiv (i,j))).toNat),List.ofFn words),i.val)=
      List.ofFn (fun j => cornerFree R P d finProdFinEquiv a (i,j)+
        scaledWordValue (integerWidth R P d (i,j),words (finProdFinEquiv (i,j)))) := by
  have hcols : scaleColumns (exponentDataCode R P d
      (fun i j => (corner a (finProdFinEquiv (i,j))).toNat))=List.range n := by
    simp only [scaleColumns,exponentDataCode,marginCode,List.tail_cons,List.length_ofFn]
  unfold offsetRow
  rw [hcols]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro j hj _
    have hjn : j<n := by simpa only [List.length_map,List.length_range] using hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,offsetRowEntry]
    exact offsetFreeEntry_code R P d a words i ⟨j,hjn⟩

theorem offsetMatrix_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (a : Grid (I := Fin (m*n)) K) (words : Fin (m*n) → List Bool) :
    offsetMatrix (exponentDataCode R P d
      (fun i j => (corner a (finProdFinEquiv (i,j))).toNat),List.ofFn words)=
      matrixCode (fun i j => cornerFree R P d finProdFinEquiv a (i,j)+
        scaledWordValue (integerWidth R P d (i,j),words (finProdFinEquiv (i,j)))) := by
  have hrows : scaleRows (exponentDataCode R P d
      (fun i j => (corner a (finProdFinEquiv (i,j))).toNat))=List.range m := by
    simp only [scaleRows,exponentDataCode,marginCode,List.tail_cons,List.length_ofFn]
  unfold offsetMatrix matrixCode
  rw [hrows]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have him : i < m := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact offsetRow_code R P d a words ⟨i,him⟩

end
end ContingencyTables.DensePrograms

end OAI
