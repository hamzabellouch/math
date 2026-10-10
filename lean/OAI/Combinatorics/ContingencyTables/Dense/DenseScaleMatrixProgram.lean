import OAI.Combinatorics.ContingencyTables.Dense.DenseScaleCellProgram

namespace OAI

/-! # Scaling a binary grid matrix to its integer bin corner -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial GridBoundary

def scaleRows (z : ExponentData) : List ℕ := List.range z.1.1.1.tail.length
def scaleColumns (z : ExponentData) : List ℕ := List.range z.1.1.2.tail.length

def scaleRowsRealizer : Realizer scaleRows :=
  composition (composition (composition (composition (composition first first) first) tail)
    listLength) range

def scaleColumnsRealizer : Realizer scaleColumns :=
  composition (composition (composition (composition (composition first first) second) tail)
    listLength) range

lemma polynomial_scaleRows : PolynomialTime scaleRowsRealizer := by
  change PolynomialTime (composition _ range)
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      polynomial_tail) polynomial_listLength) X
  intro z
  have h := list_length_le_weight z.1.1.1
  simp only [Function.comp_apply,eval_X,List.length_tail]
  exact (Nat.sub_le _ _).trans (h.trans ((weight_fst z.1.1).trans
    ((weight_fst z.1).trans (weight_fst z))))

lemma polynomial_scaleColumns : PolynomialTime scaleColumnsRealizer := by
  change PolynomialTime (composition _ range)
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_tail) polynomial_listLength) X
  intro z
  have h := list_length_le_weight z.1.1.2
  simp only [Function.comp_apply,eval_X,List.length_tail]
  exact (Nat.sub_le _ _).trans (h.trans ((weight_snd z.1.1).trans
    ((weight_fst z.1).trans (weight_fst z))))

def scaleRowEntry (z : (ExponentData×ℕ)×ℕ) : ℕ :=
  gridCellValue (z.1.1,(z.1.2,z.2))

def scaleRowEntryRealizer : Realizer scaleRowEntry :=
  composition (pair (composition first first) (pair (composition first second) second))
    gridCellValueRealizer

lemma polynomial_scaleRowEntry : PolynomialTime scaleRowEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second))
    polynomial_gridCellValue

def scaleRow (z : ExponentData×ℕ) : List ℕ :=
  (scaleColumns z.1).map (fun j => scaleRowEntry (z,j))

def scaleRowRealizer : Realizer scaleRow :=
  composition (pair identity (composition first scaleColumnsRealizer)) (mapWith scaleRowEntryRealizer)

lemma polynomial_scaleRow : PolynomialTime scaleRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_scaleColumns))
    (polynomial_mapWith polynomial_scaleRowEntry)

def scaleMatrix (z : ExponentData) : MatrixCode :=
  (scaleRows z).map (fun i => scaleRow (z,i))

def scaleMatrixRealizer : Realizer scaleMatrix :=
  composition (pair identity scaleRowsRealizer) (mapWith scaleRowRealizer)

theorem polynomial_scaleMatrix : PolynomialTime scaleMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_scaleRows)
    (polynomial_mapWith polynomial_scaleRow)

variable {m n q K : ℕ}

private lemma scaleRow_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (a : Grid (I := Fin q) K) (e : Fin m×Fin n ≃ Fin q) (i : Fin m) :
    scaleRow (exponentDataCode R P d (fun i j => (corner a (e (i,j))).toNat),i.val)=
      List.ofFn (fun j => cornerFree R P d e a (i,j)) := by
  have hcol : scaleColumns (exponentDataCode R P d
      (fun i j => (corner a (e (i,j))).toNat))=List.range n := by
    simp only [scaleColumns,exponentDataCode,marginCode,List.tail_cons,List.length_ofFn]
  unfold scaleRow
  rw [hcol]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro j hj _
    have hjn : j < n := by simpa only [List.length_map,List.length_range] using hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,scaleRowEntry]
    exact gridCellValue_code R P d a e i ⟨j,hjn⟩

/-- Every free entry is the integer width times the selected grid corner. -/
theorem scaleMatrix_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (a : Grid (I := Fin q) K) (e : Fin m×Fin n ≃ Fin q) :
    scaleMatrix (exponentDataCode R P d (fun i j => (corner a (e (i,j))).toNat))=
      matrixCode (fun i j => cornerFree R P d e a (i,j)) := by
  have hrow : scaleRows (exponentDataCode R P d
      (fun i j => (corner a (e (i,j))).toNat))=List.range m := by
    simp only [scaleRows,exponentDataCode,marginCode,List.tail_cons,List.length_ofFn]
  unfold scaleMatrix matrixCode
  rw [hrow]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have him : i < m := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact scaleRow_code R P d a e ⟨i,him⟩

end ContingencyTables.DensePrograms

end OAI
