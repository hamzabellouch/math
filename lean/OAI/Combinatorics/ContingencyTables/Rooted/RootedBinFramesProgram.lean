import OAI.Combinatorics.ContingencyTables.Machines.BinVectorProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedCatalogGrid

namespace OAI

/-! # Preparing the actual bin draws from the computed free-cell catalog

Only the capacity matrix, catalog metadata, grid coordinate list and
numeric sampling parameters are supplied. The program computes each
full range and bin index before invoking the proved vector draw.
-/

namespace ContingencyTables.RootedBinFramesProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped BigOperators Classical

/-- `(K,(precision,dimension))` and the catalog metadata/current bin. -/
abbrev Input := (ℕ×(ℕ×ℕ))×(RootedForestCatalog.Data×List ℕ)

def catalog (z : Input) : List (ℕ×ℕ) := RootedForestCatalog.catalog (z.2.1,false)
def catalogRealizer : Realizer catalog :=
  composition (f := fun z : Input => (z.2.1,false)) (g := RootedForestCatalog.catalog)
    (pair (composition second first) (constant false)) RootedForestCatalog.catalogRealizer
lemma polynomial_catalog : PolynomialTime catalogRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_constant false)) RootedForestCatalog.polynomial_catalog

def cell (z : Input×ℕ) : ℕ×ℕ := (catalog z.1).getD z.2 (0,0)
def cellRealizer : Realizer cell :=
  composition (pair (composition first catalogRealizer) second) (getDFast (0,0))
lemma polynomial_cell : PolynomialTime cellRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_catalog)
    polynomial_second) (polynomial_getDFast (0,0))

def rangeSize (z : Input×ℕ) : ℕ := matrixEntry (z.1.2.1.2,cell z)+1
def rangeSizeRealizer : Realizer rangeSize :=
  composition (composition (f := fun z : Input×ℕ => (z.1.2.1.2,cell z))
    (g := matrixEntry)
    (pair (composition (composition (composition first second) first) second) cellRealizer)
    matrixEntryRealizer) successor
lemma polynomial_rangeSize : PolynomialTime rangeSizeRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_first) polynomial_second)
    polynomial_cell) polynomial_matrixEntry) polynomial_successor

def coordinate (z : Input×ℕ) : ℕ := z.1.2.2.getD z.2 0
def coordinateRealizer : Realizer coordinate :=
  composition (pair (composition (composition first second) second) second) (getDFast 0)
lemma polynomial_coordinate : PolynomialTime coordinateRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_first polynomial_second) polynomial_second) polynomial_second)
    (polynomial_getDFast 0)

def item (z : Input×ℕ) : BinVectorProgram.Frame :=
  (((z.1.1.1,rangeSize z),coordinate z),z.1.1.2)
def itemRealizer : Realizer item :=
  pair (pair (pair (composition (composition first first) first) rangeSizeRealizer)
    coordinateRealizer) (composition (composition first first) second)
lemma polynomial_item : PolynomialTime itemRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_rangeSize) polynomial_coordinate)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)

def indices (z : Input) : List ℕ := List.range (catalog z).length
def indicesRealizer : Realizer indices :=
  composition (f := catalog) (g := RootedTreeInputProgram.indices)
    catalogRealizer RootedTreeInputProgram.indicesRealizer
lemma polynomial_indices : PolynomialTime indicesRealizer :=
  polynomial_composition polynomial_catalog RootedTreeInputProgram.polynomial_indices

def frames (z : Input) : List BinVectorProgram.Frame :=
  (indices z).map (fun i => item (z,i))
def framesRealizer : Realizer frames :=
  composition (pair identity indicesRealizer) (mapWith itemRealizer)
theorem polynomial_frames : PolynomialTime framesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_item)

def draw (z : Input×List Bool) : List ℕ := BinVectorProgram.output (frames z.1,z.2)
def drawRealizer : Realizer draw :=
  composition (f := fun z : Input×List Bool => (frames z.1,z.2)) (g := BinVectorProgram.output)
    (pair (composition first framesRealizer) second) BinVectorProgram.outputRealizer
theorem polynomial_draw : PolynomialTime drawRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_frames)
    polynomial_second) BinVectorProgram.polynomial_output

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary

noncomputable section
variable {m n K : ℕ}

def data (A : Instance (Fin m) (Fin n)) (h : ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) : Input :=
  ((K,(h,A.d)),(RootedForestCatalog.data A,gridNatCode v))

lemma catalog_data (A : Instance (Fin m) (Fin n)) (h : ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    catalog (data A h v)=List.ofFn (fun i =>
      ((RootedForestCatalog.freeEquiv A i).val.1.val,
        (RootedForestCatalog.freeEquiv A i).val.2.val)) :=
  RootedTreeInputProgram.freeCatalog_ofFn A

lemma cell_data (A : Instance (Fin m) (Fin n)) (h : ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (i : Fin (RootedCatalogGrid.freeCount A)) :
    cell (data A h v,i.val)=
      ((RootedForestCatalog.freeEquiv A i).val.1.val,
        (RootedForestCatalog.freeEquiv A i).val.2.val) := by
  rw [cell,catalog_data]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,
    Option.getD_some,Fin.eta]

lemma rangeSize_data (A : Instance (Fin m) (Fin n)) (h : ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (i : Fin (RootedCatalogGrid.freeCount A)) :
    rangeSize (data A h v,i.val)=CompanionOracleDensity.freeRange A (RootedForestCatalog.freeEquiv A i) := by
  change matrixEntry (matrixCode A.b,cell (data A h v,i.val))+1=_
  rw [cell_data,matrixEntry_code]
  rfl

lemma item_data (A : Instance (Fin m) (Fin n)) (h : ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (i : Fin (RootedCatalogGrid.freeCount A)) :
    item (data A h v,i.val)=
      (((K,CompanionOracleDensity.freeRange A (RootedForestCatalog.freeEquiv A i)),
        (v i).val.toNat),(h,A.d)) := by
  rw [item,rangeSize_data]
  simp only [coordinate,data,gridNatCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,dite_true,Option.getD_some,Fin.eta]
  rfl

theorem frames_data (A : Instance (Fin m) (Fin n)) (h : ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    frames (data A h v)=List.ofFn (fun i =>
      (((K,CompanionOracleDensity.freeRange A (RootedForestCatalog.freeEquiv A i)),
        (v i).val.toNat),(h,A.d))) := by
  apply List.ext_getElem
  · simp only [frames,indices,catalog_data,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hin : i<RootedCatalogGrid.freeCount A := by
      simpa only [List.length_ofFn] using hj
    simp only [frames,indices,catalog_data,List.length_ofFn,
      List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact item_data A h v ⟨i,hin⟩

end
end ContingencyTables.RootedBinFramesProgram

end OAI
