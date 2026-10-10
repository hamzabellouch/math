import OAI.Combinatorics.ContingencyTables.Machines.ListSubtractProgram

namespace OAI

/-! # Executable subtraction of a lower bound from a capacity matrix -/

namespace ContingencyTables.LowerCapacityProgram

open MatchingFPRAS.TreeTyped Polynomial ResidualGraphProgram

abbrev Input := (NatMatrix×(ℕ×ℕ))×ℕ
abbrev RowInput := Input×ℕ

def readRow (z : RowInput) : List ℕ := z.1.1.1.getD z.2 []

def readRowRealizer : Realizer readRow :=
  composition (pair (composition (composition first first) first) second) (getDFast [])

lemma polynomial_readRow : PolynomialTime readRowRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_first) polynomial_second) (polynomial_getDFast [])

def selected (z : RowInput) : Bool := decide (z.2=z.1.1.2.1)

def selectedRealizer : Realizer selected :=
  composition (pair second (composition (composition (composition first first) second) first)) natEqual

lemma polynomial_selected : PolynomialTime selectedRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_first)) polynomial_natEqual

def shiftedInput (z : RowInput) : ListSubtractProgram.Input :=
  ((readRow z,z.1.1.2.2),z.1.2)

def shiftedInputRealizer : Realizer shiftedInput :=
  pair (pair readRowRealizer
    (composition (composition (composition first first) second) second))
    (composition first second)

lemma polynomial_shiftedInput : PolynomialTime shiftedInputRealizer :=
  polynomial_pair (polynomial_pair polynomial_readRow
    (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_second))
    (polynomial_composition polynomial_first polynomial_second)

def row (z : RowInput) : List ℕ :=
  if z.2=z.1.1.2.1 then ListSubtractProgram.subtractAt (shiftedInput z) else readRow z

def rowRealizer : Realizer row :=
  (choose selectedRealizer
    (composition (f := shiftedInput) (g := ListSubtractProgram.subtractAt)
      shiftedInputRealizer ListSubtractProgram.subtractAtRealizer) readRowRealizer).congr (by
        intro z
        simp only [Function.comp_apply,row,selected,decide_eq_true_eq])

lemma polynomial_row : PolynomialTime rowRealizer :=
  polynomial_congr _ (polynomial_choose polynomial_selected
    (polynomial_composition polynomial_shiftedInput ListSubtractProgram.polynomial_subtractAt)
    polynomial_readRow)

def indices (z : Input) : List ℕ := List.range z.1.1.length

def indicesRealizer : Realizer indices :=
  composition (composition (composition first first) listLength) range

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

def matrix (z : Input) : NatMatrix := (indices z).map (fun i=>row (z,i))
def matrixRealizer : Realizer matrix :=
  composition (pair identity indicesRealizer) (mapWith rowRealizer)
lemma polynomial_matrix : PolynomialTime matrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_row)

lemma matrix_code {m n : ℕ} (b : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n) (t : ℕ) :
    matrix ((natCode b,(i₀.val,j₀.val)),t)=natCode (BoundedCellShift.lower b i₀ j₀ t) := by
  simp only [matrix,indices,natCode,List.length_ofFn,DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,
    List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  have hr : readRow ((((List.ofFn (fun i=>List.ofFn (b i)),(i₀.val,j₀.val)),t),i.val))=
      List.ofFn (b i) := by
    simp only [readRow,List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,
      dite_true,Option.getD_some,Fin.eta]
  by_cases hi : i=i₀
  · subst i
    simp only [row,ite_true,shiftedInput,hr]
    rw [ListSubtractProgram.subtractAt_ofFn]
    apply congrArg List.ofFn
    funext j
    simp [BoundedCellShift.margin,BoundedCellShift.lower]
  · have hn : i.val≠i₀.val := fun he=>hi (Fin.ext he)
    simp only [row,hn,ite_false,hr]
    apply congrArg List.ofFn
    funext j
    simp [BoundedCellShift.lower,hi]

end ContingencyTables.LowerCapacityProgram

end OAI
