import OAI.Combinatorics.ContingencyTables.Rooted.RootedCellDataProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionCellCatalogProgram

namespace OAI

/-! # Computing the tree and free-cell catalogs

Both catalogs scan the rectangular cell array. A free cell is selected
by its binary capacity and absence from the supplied forest graph; a
tree cell is selected by graph adjacency. Empty forests need no chosen
edge and are handled by the same program.
-/

namespace ContingencyTables.RootedForestCatalog

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open RootedCoefficientProgram FiniteGraphRootProgram
open scoped Classical

abbrev Data := ((GraphCode×ℕ)×(List ℕ×List ℕ))×MatrixCode
abbrev Item := Data×(ℕ×ℕ)

def edge (z : Item) : GraphCode×(ℕ×ℕ) :=
  (z.1.1.1.1,(z.2.1,z.1.1.2.1.length+z.2.2))
def edgeRealizer : Realizer edge :=
  pair (composition (composition (composition first first) first) first)
    (pair (composition second first)
      (composition (pair (composition (composition (composition (composition first first) second) first)
        listLength) (composition second second)) add))
lemma polynomial_edge : PolynomialTime edgeRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_pair (polynomial_composition polynomial_second polynomial_first)
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition (polynomial_composition
          (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first)
          polynomial_listLength)
        (polynomial_composition polynomial_second polynomial_second)) polynomial_add))

def treeTest (z : Item) : Bool := adjacent (edge z)
def treeTestRealizer : Realizer treeTest := composition edgeRealizer adjacentRealizer
lemma polynomial_treeTest : PolynomialTime treeTestRealizer :=
  polynomial_composition polynomial_edge polynomial_adjacent

def largeTest (z : Item) : Bool :=
  decide (z.1.1.1.2 ≤ matrixEntry (z.1.2,z.2))
def largeTestRealizer : Realizer largeTest :=
  composition (pair (composition (composition (composition first first) first) second)
    (composition (pair (composition first second) second) matrixEntryRealizer)) leNat
lemma polynomial_largeTest : PolynomialTime largeTestRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      polynomial_matrixEntry)) polynomial_leNat

def freeTest (z : Item) : Bool := largeTest z && !treeTest z
def freeTestRealizer : Realizer freeTest :=
  composition (pair largeTestRealizer (composition treeTestRealizer boolNot)) boolAnd
lemma polynomial_freeTest : PolynomialTime freeTestRealizer :=
  polynomial_composition (polynomial_pair polynomial_largeTest
    (polynomial_composition polynomial_treeTest polynomial_boolNot)) polynomial_boolAnd

def selectedTest (z : (Data×Bool)×(ℕ×ℕ)) : Bool :=
  if z.1.2 then treeTest (z.1.1,z.2) else freeTest (z.1.1,z.2)
def selectedTestRealizer : Realizer selectedTest :=
  choose (composition first second)
    (composition (f := fun z : (Data×Bool)×(ℕ×ℕ) => (z.1.1,z.2)) (g := treeTest)
      (pair (composition first first) second) treeTestRealizer)
    (composition (f := fun z : (Data×Bool)×(ℕ×ℕ) => (z.1.1,z.2)) (g := freeTest)
      (pair (composition first first) second) freeTestRealizer)
lemma polynomial_selectedTest : PolynomialTime selectedTestRealizer :=
  polynomial_choose (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) polynomial_treeTest)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) polynomial_freeTest)

def catalog (z : Data×Bool) : List (ℕ×ℕ) :=
  (cellPairs z.1.1.2).filter (fun a => selectedTest (z,a))
def catalogRealizer : Realizer catalog :=
  composition (pair identity (composition (composition (composition first first) second)
    cellPairsRealizer)) (filterWith selectedTestRealizer)
theorem polynomial_catalog : PolynomialTime catalogRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition (polynomial_composition polynomial_first
      polynomial_first) polynomial_second) polynomial_cellPairs))
    (polynomial_filterWith polynomial_selectedTest)

lemma catalog_nodup (z : Data×Bool) : (catalog z).Nodup :=
  (cellPairs_nodup z.1.1.2.1 z.1.1.2.2).filter _

open CompanionFactorialApplication ForestAssignmentSplit GraphCompletionCounts

noncomputable def data {m n : ℕ} (A : Instance (Fin m) (Fin n)) : Data :=
  (((graphCode (A.T.comap finSumFinEquiv.symm),A.W),
    (List.ofFn (fun i => (A.r i).toNat),List.ofFn (fun j => (A.c j).toNat))),matrixCode A.b)

lemma treeTest_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (i : Fin m) (j : Fin n) :
    treeTest (data A,(i.val,j.val))=decide (A.T.Adj (.inl i) (.inr j)) := by
  change adjacent (graphCode (A.T.comap finSumFinEquiv.symm),
    (i.val,(List.ofFn (fun k => (A.r k).toNat)).length+j.val))=_
  rw [List.length_ofFn]
  have he := adjacent_graph (A.T.comap finSumFinEquiv.symm)
    (finSumFinEquiv (m := m) (n := n) (.inl i))
    (finSumFinEquiv (m := m) (n := n) (.inr j))
  simpa only [SimpleGraph.comap_adj,Equiv.symm_apply_apply,finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right,Fin.val_castAdd,Fin.val_natAdd,
    finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd] using he

lemma freeTest_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (i : Fin m) (j : Fin n) :
    freeTest (data A,(i.val,j.val))=
      decide (A.small i j=false ∧ ¬A.T.Adj (.inl i) (.inr j)) := by
  have hlarge : A.W≤A.b i j ↔ A.small i j=false := by
    cases hs : A.small i j with
    | false => exact ⟨fun _ => rfl,fun _ => (A.hlarge _ _ hs).1⟩
    | true => simp only [Bool.true_eq_false,iff_false]; exact Nat.not_le.mpr (A.hsmall _ _ hs)
  unfold freeTest largeTest
  rw [treeTest_data]
  simp only [data,matrixEntry_code]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not,hlarge]

def Selected {m n : ℕ} (A : Instance (Fin m) (Fin n)) (tree : Bool) (a : Fin m×Fin n) : Prop :=
  if tree then A.T.Adj (.inl a.1) (.inr a.2)
  else A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)

abbrev Cell {m n : ℕ} (A : Instance (Fin m) (Fin n)) (tree : Bool) :=
  {a : Fin m×Fin n // Selected A tree a}

lemma selectedTest_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (tree : Bool)
    (i : Fin m) (j : Fin n) :
    selectedTest ((data A,tree),(i.val,j.val))=decide (Selected A tree (i,j)) := by
  cases tree <;> simp only [selectedTest,Selected,Bool.false_eq_true,ite_false,ite_true,
    treeTest_data,freeTest_data]

lemma mem_catalog_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (tree : Bool)
    (ij : ℕ×ℕ) : ij∈catalog (data A,tree) ↔ ∃ a : Cell A tree,(a.val.1.val,a.val.2.val)=ij := by
  rw [catalog,List.mem_filter]
  change (ij∈cellPairs (List.ofFn (fun i => (A.r i).toNat),
    List.ofFn (fun j => (A.c j).toNat)) ∧ selectedTest ((data A,tree),ij)=true) ↔ _
  rw [mem_cellPairs]
  simp only [List.length_ofFn]
  constructor
  · rintro ⟨⟨hi,hj⟩,hs⟩
    let i : Fin m := ⟨ij.1,hi⟩
    let j : Fin n := ⟨ij.2,hj⟩
    have hp : Selected A tree (i,j) := by
      apply of_decide_eq_true
      rwa [←selectedTest_data]
    exact ⟨⟨(i,j),hp⟩,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨⟨a.val.1.isLt,a.val.2.isLt⟩,
      (selectedTest_data A tree a.val.1 a.val.2).trans (decide_eq_true a.property)⟩

noncomputable def catalogCell {m n : ℕ} (A : Instance (Fin m) (Fin n)) (tree : Bool)
    (i : Fin (catalog (data A,tree)).length) : Cell A tree :=
  Classical.choose ((mem_catalog_data A tree _).mp (List.getElem_mem i.isLt))

lemma catalogCell_coordinates {m n : ℕ} (A : Instance (Fin m) (Fin n)) (tree : Bool)
    (i : Fin (catalog (data A,tree)).length) :
    ((catalogCell A tree i).val.1.val,(catalogCell A tree i).val.2.val)=
      (catalog (data A,tree))[i.val] :=
  Classical.choose_spec ((mem_catalog_data A tree _).mp (List.getElem_mem i.isLt))

lemma catalogCell_bijective {m n : ℕ} (A : Instance (Fin m) (Fin n)) (tree : Bool) :
    Function.Bijective (catalogCell A tree) := by
  constructor
  · intro i j h
    have he := congrArg (fun a : Cell A tree => (a.val.1.val,a.val.2.val)) h
    rw [catalogCell_coordinates,catalogCell_coordinates] at he
    exact Fin.ext ((catalog_nodup (data A,tree)).getElem_inj_iff.mp he)
  · intro a
    have hm : (a.val.1.val,a.val.2.val)∈catalog (data A,tree) :=
      (mem_catalog_data A tree _).mpr ⟨a,rfl⟩
    obtain ⟨i,hi,hval⟩ := List.mem_iff_getElem.mp hm
    refine ⟨⟨i,hi⟩,?_⟩
    have he := (catalogCell_coordinates A tree ⟨i,hi⟩).trans hval
    apply Subtype.ext
    exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

noncomputable def freeEquiv {m n : ℕ} (A : Instance (Fin m) (Fin n)) :
    Fin (catalog (data A,false)).length ≃ FreeCell A.small A.T :=
  Equiv.ofBijective (catalogCell A false) (catalogCell_bijective A false)

noncomputable def treeEquiv {m n : ℕ} (A : Instance (Fin m) (Fin n)) :
    Fin (catalog (data A,true)).length ≃ TreeCell A.T :=
  Equiv.ofBijective (catalogCell A true) (catalogCell_bijective A true)

end ContingencyTables.RootedForestCatalog

end OAI
