import OAI.Combinatorics.ContingencyTables.Machines.LowerCapacityProgram
import OAI.Combinatorics.MatchingCount.Machines.TreeFiniteOps

namespace OAI

/-! # The executed feasibility test with one extra lower cell bound -/

namespace ContingencyTables.CellLowerTestProgram

open MatchingFPRAS.TreeTyped Polynomial

abbrev Context := NetworkVertexCode.Input×(ℕ×ℕ)
abbrev Input := Context×ℕ

def shifted (z : Input) : NetworkVertexCode.Input :=
  ((ListSubtractProgram.subtractAt ((z.1.1.1.1,z.1.2.1),z.2),
    ListSubtractProgram.subtractAt ((z.1.1.1.2,z.1.2.2),z.2)),
    LowerCapacityProgram.matrix ((z.1.1.2,z.1.2),z.2))

def rowInputRealizer : Realizer (fun z : Input=>((z.1.1.1.1,z.1.2.1),z.2)) :=
  pair (pair (composition (composition (composition first first) first) first)
    (composition (composition first second) first)) second

def columnInputRealizer : Realizer (fun z : Input=>((z.1.1.1.2,z.1.2.2),z.2)) :=
  pair (pair (composition (composition (composition first first) first) second)
    (composition (composition first second) second)) second

def capacityInputRealizer : Realizer (fun z : Input=>((z.1.1.2,z.1.2),z.2)) :=
  pair (pair (composition (composition first first) second) (composition first second)) second

lemma polynomial_rowInput : PolynomialTime rowInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first))
    polynomial_second

lemma polynomial_columnInput : PolynomialTime columnInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second))
    polynomial_second

lemma polynomial_capacityInput : PolynomialTime capacityInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_second

def shiftedRealizer : Realizer shifted :=
  pair (pair
    (composition (f := fun z : Input=>((z.1.1.1.1,z.1.2.1),z.2))
      (g := ListSubtractProgram.subtractAt) rowInputRealizer ListSubtractProgram.subtractAtRealizer)
    (composition (f := fun z : Input=>((z.1.1.1.2,z.1.2.2),z.2))
      (g := ListSubtractProgram.subtractAt) columnInputRealizer ListSubtractProgram.subtractAtRealizer))
    (composition (f := fun z : Input=>((z.1.1.2,z.1.2),z.2))
      (g := LowerCapacityProgram.matrix) capacityInputRealizer LowerCapacityProgram.matrixRealizer)

lemma polynomial_shifted : PolynomialTime shiftedRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_rowInput ListSubtractProgram.polynomial_subtractAt)
    (polynomial_composition polynomial_columnInput ListSubtractProgram.polynomial_subtractAt))
    (polynomial_composition polynomial_capacityInput LowerCapacityProgram.polynomial_matrix)

def guards (z : Input) : Bool :=
  decide (z.2≤z.1.1.1.1.getD z.1.2.1 0) &&
    (decide (z.2≤z.1.1.1.2.getD z.1.2.2 0) &&
      decide (z.2≤ResidualGraphProgram.capacityEntry (z.1.1.2,z.1.2)))

def guardsRealizer : Realizer guards := by
  let rowBound : Realizer (fun z : Input=>z.1.1.1.1.getD z.1.2.1 0) :=
    composition (composition rowInputRealizer first) (getDFast 0)
  let columnBound : Realizer (fun z : Input=>z.1.1.1.2.getD z.1.2.2 0) :=
    composition (composition columnInputRealizer first) (getDFast 0)
  let capacityBound : Realizer (fun z : Input=>ResidualGraphProgram.capacityEntry (z.1.1.2,z.1.2)) :=
    composition (composition capacityInputRealizer first) ResidualGraphProgram.capacityEntryRealizer
  exact composition (pair (composition (pair second rowBound) leNat)
    (composition (pair (composition (pair second columnBound) leNat)
      (composition (pair second capacityBound) leNat)) boolAnd)) boolAnd

lemma polynomial_guards : PolynomialTime guardsRealizer := by
  unfold guardsRealizer
  apply polynomial_composition
  · apply polynomial_pair
    · exact polynomial_composition (polynomial_pair polynomial_second
        (polynomial_composition (polynomial_composition polynomial_rowInput polynomial_first)
          (polynomial_getDFast 0))) polynomial_leNat
    · apply polynomial_composition
      · apply polynomial_pair
        · exact polynomial_composition (polynomial_pair polynomial_second
            (polynomial_composition (polynomial_composition polynomial_columnInput polynomial_first)
              (polynomial_getDFast 0))) polynomial_leNat
        · exact polynomial_composition (polynomial_pair polynomial_second
            (polynomial_composition (polynomial_composition polynomial_capacityInput polynomial_first)
              ResidualGraphProgram.polynomial_capacityEntry)) polynomial_leNat
      · exact polynomial_boolAnd
  · exact polynomial_boolAnd

def test (z : Input) : Bool := guards z && NetworkFeasibilityProgram.test (shifted z)

def testRealizer : Realizer test :=
  composition (pair guardsRealizer
    (composition (f := shifted) (g := NetworkFeasibilityProgram.test)
      shiftedRealizer NetworkFeasibilityProgram.testRealizer)) boolAnd

lemma polynomial_test : PolynomialTime testRealizer :=
  polynomial_composition (polynomial_pair polynomial_guards
    (polynomial_composition polynomial_shifted NetworkFeasibilityProgram.polynomial_test))
    polynomial_boolAnd

lemma shifted_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) (t : ℕ) :
    shifted ((NetworkVertexCode.data r c b,(i.val,j.val)),t)=
      NetworkVertexCode.data (BoundedCellShift.margin r i t)
        (BoundedCellShift.margin c j t) (BoundedCellShift.lower b i j t) := by
  unfold shifted NetworkVertexCode.data
  rw [ListSubtractProgram.subtractAt_ofFn,ListSubtractProgram.subtractAt_ofFn,
    LowerCapacityProgram.matrix_code]

lemma guards_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) (t : ℕ) :
    guards ((NetworkVertexCode.data r c b,(i.val,j.val)),t)=true ↔
      t≤r i ∧ t≤c j ∧ t≤b i j := by
  dsimp only [guards, NetworkVertexCode.data]
  rw [ResidualGraphProgram.capacityEntry_code]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,j.isLt,dite_true,Option.getD_some,Fin.eta,Bool.and_eq_true]
  constructor
  · rintro ⟨hr,hc,hb⟩
    exact ⟨_root_.of_decide_eq_true hr,_root_.of_decide_eq_true hc,_root_.of_decide_eq_true hb⟩
  · rintro ⟨hr,hc,hb⟩
    exact ⟨_root_.decide_eq_true hr,_root_.decide_eq_true hc,_root_.decide_eq_true hb⟩

theorem test_correct {m n : ℕ} (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) (t : ℕ) :
    test ((NetworkVertexCode.data r c b,(i.val,j.val)),t)=true ↔
      ∃ X,HasMargins X r c ∧ (∀ u v,X u v≤b u v) ∧ t≤X i j := by
  rw [test,Bool.and_eq_true,guards_code,shifted_code,NetworkFeasibilityProgram.test_correct hEK]
  simpa only [and_assoc] using (BoundedCellShift.feasible_lower_iff r c b i j t).symm

end ContingencyTables.CellLowerTestProgram

end OAI
