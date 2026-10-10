import OAI.Combinatorics.ContingencyTables.Counting.CompanionCellCatalogProgram
import OAI.Combinatorics.ContingencyTables.Machines.WeightedArgmaxProgram
import OAI.Combinatorics.ContingencyTables.Transport.NetworkVertexCode

namespace OAI

/-! # The executed weighted catalog of large cells

Rows and columns are indexed by their stored margin-list lengths. The
catalog contains each retained large cell once, with its actual binary
capacity and its row/column graph endpoints.
-/

namespace ContingencyTables.LargeEdgeCatalogProgram

open MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms WeightedArgmaxProgram

abbrev Input := CompanionCellCatalog.Input
abbrev CellInput := Input×(ℕ×ℕ)

def vertexCount (z : Input) : ℕ := z.1.1.1.length+z.1.1.2.length
def vertexCountRealizer : Realizer vertexCount :=
  composition (pair
    (composition (composition (composition first first) first) listLength)
    (composition (composition (composition first first) second) listLength)) add
lemma polynomial_vertexCount : PolynomialTime vertexCountRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      polynomial_listLength)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_listLength)) polynomial_add

def endpoints (z : CellInput) : ℕ×ℕ := (z.2.1,z.1.1.1.1.length+z.2.2)
def endpointsRealizer : Realizer endpoints :=
  pair (composition second first)
    (composition (pair
      (composition (composition (composition (composition first first) first) first) listLength)
      (composition second second)) add)
lemma polynomial_endpoints : PolynomialTime endpointsRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_first)
        polynomial_first) polynomial_listLength)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_add)

def entry (z : CellInput) : Edge := (endpoints z,CompanionCellCatalog.entry z)
def entryRealizer : Realizer entry := pair endpointsRealizer CompanionCellCatalog.entryRealizer
lemma polynomial_entry : PolynomialTime entryRealizer :=
  polynomial_pair polynomial_endpoints CompanionCellCatalog.polynomial_entry

def large (z : CellInput) : Bool := !CompanionCellCatalog.retainedTest z
def largeRealizer : Realizer large :=
  composition CompanionCellCatalog.retainedTestRealizer boolNot
lemma polynomial_large : PolynomialTime largeRealizer :=
  polynomial_composition CompanionCellCatalog.polynomial_retainedTest polynomial_boolNot

def cells (z : Input) : List (ℕ×ℕ) :=
  (cellPairs z.1.1).filter (fun a=>large (z,a))
def cellsRealizer : Realizer cells :=
  composition (pair identity (composition (composition first first) cellPairsRealizer))
    (filterWith largeRealizer)
lemma polynomial_cells : PolynomialTime cellsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_cellPairs)) (polynomial_filterWith polynomial_large)

def catalog (z : Input) : List Edge := (cells z).map (fun a=>entry (z,a))
def catalogRealizer : Realizer catalog :=
  composition (pair identity cellsRealizer) (mapWith entryRealizer)
lemma polynomial_catalog : PolynomialTime catalogRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_cells)
    (polynomial_mapWith polynomial_entry)

variable {m n : ℕ}

lemma entry_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (W : ℕ) (i : Fin m) (j : Fin n) :
    entry ((NetworkVertexCode.data r c b,W),(i.val,j.val))=
      ((i.val,m+j.val),b i j) := by
  change ((i.val,(List.ofFn r).length+j.val),matrixEntry (matrixCode b,(i.val,j.val)))=_
  rw [List.length_ofFn,matrixEntry_code]

lemma mem_cells_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (W : ℕ) (a : ℕ×ℕ) :
    a∈cells (NetworkVertexCode.data r c b,W) ↔
      ∃ i : Fin m,∃ j : Fin n,a=(i.val,j.val) ∧ W≤b i j := by
  rw [cells,List.mem_filter]
  change (a∈cellPairs (List.ofFn r,List.ofFn c) ∧
    large ((NetworkVertexCode.data r c b,W),a)=true) ↔ _
  rw [mem_cellPairs]
  simp only [List.length_ofFn]
  constructor
  · rintro ⟨⟨hi,hj⟩,ht⟩
    let i : Fin m := ⟨a.1,hi⟩
    let j : Fin n := ⟨a.2,hj⟩
    refine ⟨i,j,rfl,?_⟩
    have hn : ¬CompanionCellCatalog.entry
        ((NetworkVertexCode.data r c b,W),(i.val,j.val))<W := by
      simpa only [large,CompanionCellCatalog.retainedTest,Bool.not_eq_true',
        decide_eq_false_iff_not] using ht
    have he : CompanionCellCatalog.entry
        ((NetworkVertexCode.data r c b,W),(i.val,j.val))=b i j := matrixEntry_code b i j
    rw [he] at hn
    exact Nat.le_of_not_gt hn
  · rintro ⟨i,j,rfl,hb⟩
    refine ⟨⟨i.isLt,j.isLt⟩,?_⟩
    have he : CompanionCellCatalog.entry
        ((NetworkVertexCode.data r c b,W),(i.val,j.val))=b i j := matrixEntry_code b i j
    simpa only [large,CompanionCellCatalog.retainedTest,Bool.not_eq_true',
      decide_eq_false_iff_not,he] using Nat.not_lt.mpr hb

/-- Exact source cell capacities and graph endpoints, with no finite
choice or supplied catalog-correctness hypothesis. -/
theorem mem_catalog_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (W : ℕ) (e : Edge) :
    e∈catalog (NetworkVertexCode.data r c b,W) ↔
      ∃ i : Fin m,∃ j : Fin n,W≤b i j ∧ e=((i.val,m+j.val),b i j) := by
  rw [catalog,List.mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    obtain ⟨i,j,rfl,hb⟩ := (mem_cells_code r c b W a).mp ha
    exact ⟨i,j,hb,he.symm.trans (entry_code r c b W i j)⟩
  · rintro ⟨i,j,hb,rfl⟩
    exact ⟨(i.val,j.val),(mem_cells_code r c b W _).mpr ⟨i,j,rfl,hb⟩,
      entry_code r c b W i j⟩

lemma vertexCount_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (W : ℕ) :
    vertexCount (NetworkVertexCode.data r c b,W)=m+n := by
  simp only [vertexCount,NetworkVertexCode.data,List.length_ofFn]

end ContingencyTables.LargeEdgeCatalogProgram

end OAI
