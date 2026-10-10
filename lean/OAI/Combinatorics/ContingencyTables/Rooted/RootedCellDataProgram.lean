import OAI.Combinatorics.ContingencyTables.Rooted.RootedForestDataProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseOffsetWidths

namespace OAI

/-! # Assembling the affine input from ordinary rectangular cell arrays

The baseline and both stored views are binary natural matrices. The
program reads each cell once, computes its row/column vertex indices,
and constructs the offset evaluator input in row-major order.
-/

namespace ContingencyTables.RootedCellDataProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open FiniteGraphRootProgram FiniteGraphCutProgram
open scoped Classical

abbrev Matrices := (MatrixCode×MatrixCode)×(MatrixCode×MatrixCode)
abbrev Frame := (EdgeInput×ℕ)×(List ℕ×List ℕ)
abbrev Input := Frame×Matrices
abbrev CellInput := Input×(ℕ×ℕ)

def values (z : Matrices×(ℕ×ℕ)) : (ℕ×ℕ)×(ℕ×ℕ) :=
  ((matrixEntry (z.1.1.1,z.2),matrixEntry (z.1.1.2,z.2)),
    (matrixEntry (z.1.2.1,z.2),matrixEntry (z.1.2.2,z.2)))

def valuesRealizer : Realizer values :=
  pair
    (pair
      (composition (pair (composition (composition first first) first) second) matrixEntryRealizer)
      (composition (pair (composition (composition first first) second) second) matrixEntryRealizer))
    (pair
      (composition (pair (composition (composition first second) first) second) matrixEntryRealizer)
      (composition (pair (composition (composition first second) second) second) matrixEntryRealizer))

lemma polynomial_values : PolynomialTime valuesRealizer :=
  polynomial_pair
    (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
          polynomial_first) polynomial_second) polynomial_matrixEntry)
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
          polynomial_second) polynomial_second) polynomial_matrixEntry))
    (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
          polynomial_first) polynomial_second) polynomial_matrixEntry)
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
          polynomial_second) polynomial_second) polynomial_matrixEntry))

def endpoints (z : Frame×(ℕ×ℕ)) : ℕ×ℕ :=
  (z.2.1,z.1.2.1.length+z.2.2)
def endpointsRealizer : Realizer endpoints :=
  pair (composition second first)
    (composition (pair (composition (composition (composition first second) first) listLength)
      (composition second second)) add)
lemma polynomial_endpoints : PolynomialTime endpointsRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_second) polynomial_first)
        polynomial_listLength)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_add)

def cellValues (z : CellInput) : (ℕ×ℕ)×(ℕ×ℕ) := values (z.1.2,z.2)
def cellValuesRealizer : Realizer cellValues :=
  composition (f := fun z : CellInput => (z.1.2,z.2)) (g := values)
    (pair (composition first second) second) valuesRealizer
lemma polynomial_cellValues : PolynomialTime cellValuesRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    polynomial_second) polynomial_values

def coefficientInput (z : CellInput) : RootedCoefficientProgram.Input :=
  ((z.1.1.1.1,endpoints (z.1.1,z.2)),(z.1.1.1.2,(cellValues z).1.1))
def coefficientInputRealizer : Realizer coefficientInput :=
  pair
    (pair (composition (composition (composition first first) first) first)
      (composition (pair (composition first first) second) endpointsRealizer))
    (pair (composition (composition (composition first first) first) second)
      (composition (composition cellValuesRealizer first) first))
lemma polynomial_coefficientInput : PolynomialTime coefficientInputRealizer :=
  polynomial_pair
    (polynomial_pair
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_endpoints))
    (polynomial_pair
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
      (polynomial_composition (polynomial_composition polynomial_cellValues polynomial_first)
        polynomial_first))

def entry (z : CellInput) : RootedOffsetProgram.Entry :=
  ((coefficientInput z,(((cellValues z).2.1,0),((cellValues z).2.2,0))),
    ((cellValues z).1.2,0))
def entryRealizer : Realizer entry :=
  pair (pair coefficientInputRealizer
    (pair (pair (composition (composition cellValuesRealizer second) first) (constant 0))
      (pair (composition (composition cellValuesRealizer second) second) (constant 0))))
    (pair (composition (composition cellValuesRealizer first) second) (constant 0))
lemma polynomial_entry : PolynomialTime entryRealizer :=
  polynomial_pair (polynomial_pair polynomial_coefficientInput
    (polynomial_pair
      (polynomial_pair (polynomial_composition (polynomial_composition polynomial_cellValues
        polynomial_second) polynomial_first) (polynomial_constant 0))
      (polynomial_pair (polynomial_composition (polynomial_composition polynomial_cellValues
        polynomial_second) polynomial_second) (polynomial_constant 0))))
    (polynomial_pair (polynomial_composition (polynomial_composition polynomial_cellValues
      polynomial_first) polynomial_second) (polynomial_constant 0))

def baselineCell (z : Frame) : ℕ×ℕ :=
  (z.1.1.2.1,z.1.1.2.2-z.2.1.length)
def baselineCellRealizer : Realizer baselineCell :=
  pair (composition (composition (composition first first) second) first)
    (composition (pair (composition (composition (composition first first) second) second)
      (composition (composition second first) listLength)) subtract)
lemma polynomial_baselineCell : PolynomialTime baselineCellRealizer :=
  polynomial_pair (polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second)
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
        polynomial_listLength)) polynomial_subtract)

def offsetInput (z : Input) : RootedOffsetProgram.Input :=
  ((matrixEntry (z.2.1.2,baselineCell z.1),0),
    (cellPairs z.1.2).map (fun a => entry (z,a)))
def offsetInputRealizer : Realizer offsetInput :=
  pair (pair
    (composition (pair (composition (composition second first) second)
      (composition first baselineCellRealizer)) matrixEntryRealizer) (constant 0))
    (composition (pair identity (composition (composition first second) cellPairsRealizer))
      (mapWith entryRealizer))
theorem polynomial_offsetInput : PolynomialTime offsetInputRealizer :=
  polynomial_pair
    (polynomial_pair (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_second)
      (polynomial_composition polynomial_first polynomial_baselineCell)) polynomial_matrixEntry)
      (polynomial_constant 0))
    (polynomial_composition (polynomial_pair polynomial_identity
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_cellPairs)) (polynomial_mapWith polynomial_entry))

open CompanionFactorialApplication RootedCompletion

noncomputable def data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ) : Input :=
  ((((graphCode (A.T.comap finSumFinEquiv.symm),
      ((finSumFinEquiv (m := m) (n := n) (.inl t.val.1)).val,
        (finSumFinEquiv (m := m) (n := n) (.inr t.val.2)).val)),A.W),
    (List.ofFn (fun i => (A.r i).toNat),List.ofFn (fun j => (A.c j).toNat))),
    ((matrixCode A.b,matrixCode (fun i j => (A.X i j).toNat)),(matrixCode x,matrixCode q)))

lemma values_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ)
    (i : Fin m) (j : Fin n) :
    values ((data A t x q).2,(i.val,j.val))=
      ((A.b i j,(A.X i j).toNat),(x i j,q i j)) := by
  simp only [values,data,matrixEntry_code]

lemma coefficientInput_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ)
    (i : Fin m) (j : Fin n) :
    coefficientInput (data A t x q,(i.val,j.val))=RootedCoefficientProgram.input A t (i,j) := by
  simp only [coefficientInput,cellValues,values_data]
  simp only [endpoints,data,List.length_ofFn,RootedCoefficientProgram.input,
    finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,Fin.val_castAdd,Fin.val_natAdd]

lemma entry_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ)
    (i : Fin m) (j : Fin n) :
    entry (data A t x q,(i.val,j.val))=RootedOffsetProgram.entry A t
      (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ)) (i,j) := by
  have hx : ForestAffineProgram.signedParts (A.X i j)=((A.X i j).toNat,0) := by
    unfold ForestAffineProgram.signedParts
    rw [Int.toNat_of_nonpos (neg_nonpos.mpr (A.hX i j).1)]
  simp only [entry,coefficientInput_data,cellValues,values_data,RootedOffsetProgram.entry]
  rw [hx]
  simp only [ForestAffineProgram.signedParts,Int.toNat_natCast,Int.toNat_neg_natCast]

theorem offsetInput_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ) :
    offsetInput (data A t x q)=RootedOffsetProgram.data A t
      (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ)) finProdFinEquiv.symm := by
  have hx : ForestAffineProgram.signedParts (A.X t.val.1 t.val.2)=
      ((A.X t.val.1 t.val.2).toNat,0) := by
    unfold ForestAffineProgram.signedParts
    rw [Int.toNat_of_nonpos (neg_nonpos.mpr (A.hX t.val.1 t.val.2).1)]
  unfold offsetInput RootedOffsetProgram.data
  apply Prod.ext
  · simp only [data,baselineCell,List.length_ofFn,finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right,Fin.val_castAdd,Fin.val_natAdd,
      Nat.add_sub_cancel_left,matrixEntry_code,hx]
  · change (cellPairs (List.ofFn (fun i => (A.r i).toNat),
        List.ofFn (fun j => (A.c j).toNat))).map (fun a => entry (data A t x q,a))=_
    rw [DensePrograms.cellPairs_ofFn]
    simp only [List.map_ofFn]
    congr 1
    funext k
    exact entry_data A t x q (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

end ContingencyTables.RootedCellDataProgram

end OAI
