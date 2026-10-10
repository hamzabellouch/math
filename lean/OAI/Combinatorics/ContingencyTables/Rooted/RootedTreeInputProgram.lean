import OAI.Combinatorics.ContingencyTables.Rooted.RootedDemandProgram

namespace OAI

/-! # Building tree-local inputs from the common raw arrays

The graph, capacity array, baseline and stored views are shared across
all tree terms. A term uses only its pair of cell indices; the program
builds its offset frame and reads the free-grid coordinates in catalog
order.
-/

namespace ContingencyTables.RootedTreeInputProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

abbrev Context := RootedDemandProgram.Input
abbrev Input := Context×(ℕ×ℕ)

def metadata (z : Input) : RootedForestCatalog.Data := z.1.1
def metadataRealizer : Realizer metadata := composition first first
lemma polynomial_metadata : PolynomialTime metadataRealizer :=
  polynomial_composition polynomial_first polynomial_first

def edge (z : Input) : FiniteGraphCutProgram.EdgeInput :=
  RootedForestCatalog.edge (metadata z,z.2)
def edgeRealizer : Realizer edge :=
  composition (pair metadataRealizer second) RootedForestCatalog.edgeRealizer
lemma polynomial_edge : PolynomialTime edgeRealizer :=
  polynomial_composition (polynomial_pair polynomial_metadata polynomial_second)
    RootedForestCatalog.polynomial_edge

def treeInput (z : Input) : RootedCellDataProgram.Input :=
  (((edge z,(metadata z).1.1.2),(metadata z).1.2),
    (((metadata z).2,z.1.2.1),z.1.2.2))
def treeInputRealizer : Realizer treeInput :=
  pair
    (pair (pair edgeRealizer
      (composition (f := metadata) (g := fun d : RootedForestCatalog.Data => d.1.1.2)
        metadataRealizer (composition (composition first first) second)))
      (composition (f := metadata) (g := fun d : RootedForestCatalog.Data => d.1.2)
        metadataRealizer (composition first second)))
    (pair (pair (composition (f := metadata) (g := fun d : RootedForestCatalog.Data => d.2)
      metadataRealizer second)
      (composition (composition first second) first))
      (composition (composition first second) second))
theorem polynomial_treeInput : PolynomialTime treeInputRealizer :=
  polynomial_pair
    (polynomial_pair (polynomial_pair polynomial_edge
      (polynomial_composition polynomial_metadata (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_second)))
      (polynomial_composition polynomial_metadata (polynomial_composition polynomial_first polynomial_second)))
    (polynomial_pair (polynomial_pair (polynomial_composition polynomial_metadata polynomial_second)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first))
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second))

abbrev TermBundle := (RootedCellDataProgram.Input×List (ℕ×ℕ))×List ℕ

def termAt (z : TermBundle×ℕ) : RootedForestDataProgram.TermInput :=
  (RootedCellDataProgram.coefficientInput
    (z.1.1.1,z.1.1.2.getD z.2 (0,0)),z.1.2.getD z.2 0)
def termAtRealizer : Realizer termAt :=
  pair
    (composition (f := fun z : TermBundle×ℕ => (z.1.1.1,z.1.1.2.getD z.2 (0,0)))
      (g := RootedCellDataProgram.coefficientInput)
      (pair (composition (composition first first) first)
        (composition (pair (composition (composition first first) second) second)
          (getDFast (0,0)))) RootedCellDataProgram.coefficientInputRealizer)
    (composition (pair (composition first second) second) (getDFast 0))
lemma polynomial_termAt : PolynomialTime termAtRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
        polynomial_second) (polynomial_getDFast (0,0))))
      RootedCellDataProgram.polynomial_coefficientInput)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
      polynomial_second) (polynomial_getDFast 0))

def indices (xs : List (ℕ×ℕ)) : List ℕ := List.range xs.length
def indicesRealizer : Realizer indices := composition listLength range
lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange polynomial_listLength Polynomial.X
  intro xs
  simpa only [Polynomial.eval_X] using list_length_le_weight xs

def terms (z : TermBundle) : List RootedForestDataProgram.TermInput :=
  (indices z.1.2).map (fun k => termAt (z,k))
def termsRealizer : Realizer terms :=
  composition (pair identity (composition (composition first second) indicesRealizer))
    (mapWith termAtRealizer)
theorem polynomial_terms : PolynomialTime termsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_indices)) (polynomial_mapWith polynomial_termAt)

lemma terms_ofFn {n : ℕ} (frame : RootedCellDataProgram.Input)
    (cells : Fin n → ℕ×ℕ) (v : Fin n → ℕ) :
    terms ((frame,List.ofFn cells),List.ofFn v)=
      List.ofFn (fun i => (RootedCellDataProgram.coefficientInput (frame,cells i),v i)) := by
  apply List.ext_getElem
  · simp only [terms,indices,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hin : i<n := by simpa only [List.length_ofFn] using hj
    simp only [terms,indices,List.length_ofFn,List.getElem_map,List.getElem_range,
      termAt,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hin,dite_true,Option.getD_some,
      List.getElem_ofFn]

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

theorem treeInput_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ) :
    treeInput (RootedDemandProgram.data A x q,(t.val.1.val,t.val.2.val))=
      RootedCellDataProgram.data A t x q := by
  simp only [treeInput,edge,metadata,RootedDemandProgram.data,RootedForestCatalog.edge,
    RootedForestCatalog.data,RootedCellDataProgram.data,List.length_ofFn,
    finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,Fin.val_castAdd,Fin.val_natAdd]

lemma freeCatalog_ofFn {m n : ℕ} (A : Instance (Fin m) (Fin n)) :
    RootedForestCatalog.catalog (RootedForestCatalog.data A,false)=
      List.ofFn (fun i => (((RootedForestCatalog.freeEquiv A) i).val.1.val,
        ((RootedForestCatalog.freeEquiv A) i).val.2.val)) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn]
  · intro i hi hj
    simp only [List.getElem_ofFn]
    exact (RootedForestCatalog.catalogCell_coordinates A false ⟨i,hi⟩).symm

theorem terms_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ)
    (v : FreeCell A.small A.T → ℕ) :
    terms ((treeInput (RootedDemandProgram.data A x q,(t.val.1.val,t.val.2.val)),
      RootedForestCatalog.catalog (RootedForestCatalog.data A,false)),
        List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i)))=
      List.ofFn (fun i =>
        (RootedCoefficientProgram.input A t ((RootedForestCatalog.freeEquiv A) i).val,
          v (RootedForestCatalog.freeEquiv A i))) := by
  have hf := congrArg (fun frame : RootedCellDataProgram.Input =>
    terms ((frame,RootedForestCatalog.catalog (RootedForestCatalog.data A,false)),
      List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))))
    (treeInput_data A t x q)
  have hc := congrArg (fun cells : List (ℕ×ℕ) =>
    terms ((RootedCellDataProgram.data A t x q,cells),
      List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))))
    (freeCatalog_ofFn A)
  refine hf.trans (hc.trans ((terms_ofFn (RootedCellDataProgram.data A t x q)
    (fun i => (((RootedForestCatalog.freeEquiv A) i).val.1.val,
      ((RootedForestCatalog.freeEquiv A) i).val.2.val))
    (fun i => v (RootedForestCatalog.freeEquiv A i))).trans ?_))
  apply congrArg List.ofFn
  funext i
  exact congrArg (fun z => (z,v (RootedForestCatalog.freeEquiv A i)))
    (RootedCellDataProgram.coefficientInput_data A t x q
      ((RootedForestCatalog.freeEquiv A) i).val.1 ((RootedForestCatalog.freeEquiv A) i).val.2)

end ContingencyTables.RootedTreeInputProgram

end OAI
