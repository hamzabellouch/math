import OAI.Combinatorics.ContingencyTables.Transport.PairedProfileSemantics
import OAI.Combinatorics.ContingencyTables.Machines.SparseViewMatrixProgram
import OAI.Combinatorics.ContingencyTables.Machines.MatrixSubtractProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleWalkProgram

namespace OAI

/-! # Replacing the oracle demand by the current encoded paired state

Only the retained-cell catalog and the supplied state are scanned. The
large cells receive zero in each sparse view and hence retain their full
capacity in the complemented column demand.
-/

namespace ContingencyTables.PairedDemandProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

abbrev Input := RootedDemandProgram.Input × List ℕ

def cellInput (d : RootedForestCatalog.Data) : CompanionCellCatalog.Input :=
  ((d.1.2,d.2),d.1.1.2)
def cellInputRealizer : Realizer cellInput :=
  pair (pair (composition first second) second) (composition (composition first first) second)
lemma polynomial_cellInput : PolynomialTime cellInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    polynomial_second) (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)

def cells (z : Input) : CompanionCellCatalog.Input := cellInput z.1.1
def cellsRealizer : Realizer cells :=
  composition (f := fun z : Input => z.1.1) (g := cellInput)
    (composition first first) cellInputRealizer
lemma polynomial_cells : PolynomialTime cellsRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    polynomial_cellInput

def counts (z : Input) : List (ℕ × ℕ) :=
  PairedProfileProgram.profileRows (CompanionCellCatalog.capacities (cells z),z.2)
def countsRealizer : Realizer counts :=
  composition (f := fun z : Input => (CompanionCellCatalog.capacities (cells z),z.2))
    (g := PairedProfileProgram.profileRows)
    (pair (composition (f := cells) (g := CompanionCellCatalog.capacities)
      cellsRealizer CompanionCellCatalog.capacitiesRealizer) second)
    PairedProfileProgram.profileRowsRealizer
lemma polynomial_counts : PolynomialTime countsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_cells CompanionCellCatalog.polynomial_capacities)
    polynomial_second) PairedProfileProgram.polynomial_profileRows

def sideEntry (z : Bool × (ℕ × ℕ)) : ℕ := if z.1 then z.2.2 else z.2.1
def sideEntryRealizer : Realizer sideEntry :=
  choose first (composition second second) (composition second first)
lemma polynomial_sideEntry : PolynomialTime sideEntryRealizer :=
  polynomial_choose polynomial_first
    (polynomial_composition polynomial_second polynomial_second)
    (polynomial_composition polynomial_second polynomial_first)

def values (z : Input × Bool) : List ℕ := (counts z.1).map (fun p => sideEntry (z.2,p))
def valuesRealizer : Realizer values :=
  composition (f := fun z : Input × Bool => (z.2,counts z.1))
    (g := fun p : Bool × List (ℕ × ℕ) => p.2.map (fun a => sideEntry (p.1,a)))
    (pair second (composition (f := Prod.fst) (g := counts) first countsRealizer))
    (mapWith sideEntryRealizer)
lemma polynomial_values : PolynomialTime valuesRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_first polynomial_counts))
    (polynomial_mapWith polynomial_sideEntry)

def viewInput (z : Input × Bool) : SparseViewMatrixProgram.Input :=
  (z.1.1.1.1.2,(CompanionCellCatalog.catalog (cells z.1),values z))
def viewInputRealizer : Realizer viewInput :=
  pair (composition (composition (composition (composition first first) first) first) second)
    (pair (composition (f := fun z : Input × Bool => cells z.1)
      (g := CompanionCellCatalog.catalog)
      (composition (f := Prod.fst) (g := cells) first cellsRealizer)
      CompanionCellCatalog.catalogRealizer) valuesRealizer)
lemma polynomial_viewInput : PolynomialTime viewInputRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first)
        polynomial_first) polynomial_second)
    (polynomial_pair (polynomial_composition
      (polynomial_composition polynomial_first polynomial_cells)
      CompanionCellCatalog.polynomial_catalog) polynomial_values)

def viewMatrix (z : Input × Bool) : MatrixCode := SparseViewMatrixProgram.matrix (viewInput z)
def viewMatrixRealizer : Realizer viewMatrix :=
  composition (f := viewInput) (g := SparseViewMatrixProgram.matrix)
    viewInputRealizer SparseViewMatrixProgram.matrixRealizer
lemma polynomial_viewMatrix : PolynomialTime viewMatrixRealizer :=
  polynomial_composition polynomial_viewInput SparseViewMatrixProgram.polynomial_matrix

def complement (z : Input) : MatrixCode :=
  MatrixSubtractProgram.matrix (z.1.1.2,viewMatrix (z,true))
def complementRealizer : Realizer complement :=
  composition (f := fun z : Input => (z.1.1.2,viewMatrix (z,true)))
    (g := MatrixSubtractProgram.matrix)
    (pair (composition (composition first first) second)
      (composition (f := fun z : Input => (z,true)) (g := viewMatrix)
        (pair identity (constant true)) viewMatrixRealizer)) MatrixSubtractProgram.matrixRealizer
lemma polynomial_complement : PolynomialTime complementRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second)
    (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant true))
      polynomial_viewMatrix)) MatrixSubtractProgram.polynomial_matrix

def output (z : Input) : RootedDemandProgram.Input :=
  (z.1.1,(z.1.2.1,(viewMatrix (z,false),complement z)))
def outputRealizer : Realizer output :=
  pair (composition first first)
    (pair (composition (composition first second) first)
      (pair (composition (f := fun z : Input => (z,false)) (g := viewMatrix)
        (pair identity (constant false)) viewMatrixRealizer) complementRealizer))
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_first)
      (polynomial_pair (polynomial_composition
        (polynomial_pair polynomial_identity (polynomial_constant false)) polynomial_viewMatrix)
        polynomial_complement))

noncomputable section
open CompanionFactorialApplication CompanionArithmeticProposal PairedProfileSemantics
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles SmallGraphProfiles

variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

lemma cells_data (x q : Fin m → Fin n → ℕ) (code : List ℕ) :
    cells (RootedDemandProgram.data A x q,code)=CompanionCellCatalog.input A := rfl

lemma catalog_eq :
    CompanionCellCatalog.catalog (CompanionCellCatalog.input A)=
      cellCatalog A.small (CompanionCellCatalog.cellEquiv A) := by
  rw [cellCatalog]
  symm
  calc
    List.ofFn (fun i =>
        ((CompanionCellCatalog.cellEquiv A i).val.1.val,
          (CompanionCellCatalog.cellEquiv A i).val.2.val))=
        List.ofFn (fun i : Fin (CompanionCellCatalog.catalog
          (CompanionCellCatalog.input A)).length =>
            (CompanionCellCatalog.catalog (CompanionCellCatalog.input A))[i.val]) := by
      apply congrArg List.ofFn
      funext i
      exact CompanionCellCatalog.catalogCell_coordinates A i
    _=_ := List.ofFn_get _

lemma values_data (x q : Fin m → Fin n → ℕ) (S : Set (Labels A × Bool)) (side : Bool) :
    values ((RootedDemandProgram.data A x q,
      encodeSet (CompanionComputedInitial.coordinateOrder A) S),side)=
        viewList A.small (CompanionCellCatalog.cellEquiv A)
          (CompanionWeightOracle.profile A S) side := by
  unfold values counts
  rw [cells_data,CompanionCellCatalog.capacities_eq]
  change (PairedProfileProgram.profileRows
      (List.ofFn (CompanionComputedInitial.capacities A),
        encodeSet (CompanionComputedInitial.coordinateOrder A) S)).map _=_
  rw [profileRows_physical]
  simp only [List.map_ofFn,Function.comp_def,viewList,sideEntry]
  cases side <;> rfl

lemma viewMatrix_data (x q : Fin m → Fin n → ℕ) (S : Set (Labels A × Bool)) (side : Bool) :
    viewMatrix ((RootedDemandProgram.data A x q,
      encodeSet (CompanionComputedInitial.coordinateOrder A) S),side)=
        matrixCode (smallView A.small (CompanionWeightOracle.profile A S) side) := by
  let z : Input := (RootedDemandProgram.data A x q,
    encodeSet (CompanionComputedInitial.coordinateOrder A) S)
  have hi : viewInput (z,side)=
      ((List.ofFn (fun i => (A.r i).toNat),List.ofFn (fun j => (A.c j).toNat)),
        (cellCatalog A.small (CompanionCellCatalog.cellEquiv A),
          viewList A.small (CompanionCellCatalog.cellEquiv A)
            (CompanionWeightOracle.profile A S) side)) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact (congrArg CompanionCellCatalog.catalog (cells_data A x q _)).trans (catalog_eq A)
      · exact values_data A x q S side
  change SparseViewMatrixProgram.matrix (viewInput (z,side))=_
  rw [hi]
  rw [SparseViewMatrixProgram.matrix_ofFn]
  apply congrArg matrixCode
  funext i j
  exact lookupView_eq A.small (CompanionCellCatalog.cellEquiv A)
    (CompanionWeightOracle.profile A S) side i j

/-- The current code replaces both demand arrays; the old demand only
provides the immutable graph, capacities, margins and baseline. -/
theorem output_data (x q : Fin m → Fin n → ℕ) (S : Set (Labels A × Bool)) :
    output (RootedDemandProgram.data A x q,
      encodeSet (CompanionComputedInitial.coordinateOrder A) S)=
        RootedDemandProgram.data A
          (ForestCountIdentification.smallX A.small (CompanionWeightOracle.profile A S))
          (fun i j => A.b i j-
            ForestCountIdentification.smallY A.small (CompanionWeightOracle.profile A S) i j) := by
  have hq : complement (RootedDemandProgram.data A x q,
      encodeSet (CompanionComputedInitial.coordinateOrder A) S)=
      matrixCode (fun i j => A.b i j-
        smallView A.small (CompanionWeightOracle.profile A S) true i j) := by
    change MatrixSubtractProgram.matrix (matrixCode A.b,viewMatrix
      ((RootedDemandProgram.data A x q,
        encodeSet (CompanionComputedInitial.coordinateOrder A) S),true))=_
    rw [viewMatrix_data]
    exact MatrixSubtractProgram.matrix_code _ _
  unfold output
  rw [viewMatrix_data,hq]
  rfl

end
end ContingencyTables.PairedDemandProgram

end OAI
