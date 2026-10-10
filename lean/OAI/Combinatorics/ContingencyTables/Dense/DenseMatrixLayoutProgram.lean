import OAI.Combinatorics.ContingencyTables.Dense.DenseGridExponentProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseAxisWordProgram

namespace OAI

/-! # Polynomial conversion between flat and rectangular grid encodings -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

abbrev GridFlatData := (List ℕ×List ℕ)×List ℕ

def sliceRow (z : (ℕ×List ℕ)×ℕ) : List ℕ :=
  (z.1.2.drop (z.2*z.1.1)).take z.1.1

def sliceRowRealizer : Realizer sliceRow :=
  composition (pair
    (composition (pair (composition first second)
      (composition (pair second (composition first first)) multiply)) dropFast)
    (composition first first)) takeFast

theorem polynomial_sliceRow : PolynomialTime sliceRowRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition (polynomial_pair polynomial_second
        (polynomial_composition polynomial_first polynomial_first)) polynomial_multiply))
      polynomial_dropFast)
    (polynomial_composition polynomial_first polynomial_first)) polynomial_takeFast

def layoutRows (z : GridFlatData) : List ℕ := List.range z.1.1.tail.length

def layoutRowsRealizer : Realizer layoutRows :=
  composition (composition (composition (composition first first) tail) listLength) range

theorem polynomial_layoutRows : PolynomialTime layoutRowsRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_tail) polynomial_listLength) X
  intro z
  simp only [Function.comp_apply,eval_X,List.length_tail]
  exact (Nat.sub_le _ _).trans ((list_length_le_weight z.1.1).trans
    ((weight_fst z.1).trans (weight_fst z)))

def layoutRow (z : GridFlatData×ℕ) : List ℕ :=
  sliceRow ((z.1.1.2.tail.length,z.1.2),z.2)

def layoutRowRealizer : Realizer layoutRow :=
  composition (pair (pair
    (composition (composition (composition (composition first first) second) tail) listLength)
    (composition first second)) second) sliceRowRealizer

theorem polynomial_layoutRow : PolynomialTime layoutRowRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_tail) polynomial_listLength)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_second) polynomial_sliceRow

def unflattenGrid (z : GridFlatData) : MatrixCode :=
  (layoutRows z).map (fun i => layoutRow (z,i))

def unflattenGridRealizer : Realizer unflattenGrid :=
  composition (pair identity layoutRowsRealizer) (mapWith layoutRowRealizer)

theorem polynomial_unflattenGrid : PolynomialTime unflattenGridRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_layoutRows)
    (polynomial_mapWith polynomial_layoutRow)

lemma flatten_matrixCode {m n : ℕ} (f : Fin (m*n) → ℕ) :
    (matrixCode (fun i j => f (finProdFinEquiv (i,j)))).flatten=List.ofFn f := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  apply congrArg f
  apply Fin.ext
  change j.val+n*i.val=i.val*n+j.val
  ac_rfl

lemma sliceRow_ofFn {m n : ℕ} (f : Fin (m*n) → ℕ) (i : Fin m) :
    sliceRow ((n,List.ofFn f),i.val)=
      List.ofFn (fun j : Fin n => f (finProdFinEquiv (i,j))) := by
  have hbound : n ≤ m*n-i.val*n := by
    have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
    apply Nat.le_sub_of_add_le
    simpa only [Nat.succ_mul, Nat.add_comm] using h
  apply List.ext_getElem
  · simp only [sliceRow,List.length_take,List.length_drop,List.length_ofFn,min_eq_left hbound]
  · intro j _ _
    simp only [sliceRow,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    apply congrArg f
    apply Fin.ext
    change i.val*n+j=j+n*i.val
    ac_rfl

theorem unflattenGrid_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (f : Fin (m*n) → ℕ) :
    unflattenGrid ((marginCode R,marginCode P),List.ofFn f)=
      matrixCode (fun i j => f (finProdFinEquiv (i,j))) := by
  have hrows : layoutRows ((marginCode R,marginCode P),List.ofFn f)=List.range m := by
    simp only [layoutRows,marginCode,List.tail_cons,List.length_ofFn]
  have hcols : (marginCode P).tail.length=n := by
    simp only [marginCode,List.tail_cons,List.length_ofFn]
  unfold unflattenGrid matrixCode
  rw [hrows]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have him : i < m := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,layoutRow,hcols]
    exact sliceRow_ofFn f ⟨i,him⟩

end ContingencyTables.DensePrograms

end OAI
