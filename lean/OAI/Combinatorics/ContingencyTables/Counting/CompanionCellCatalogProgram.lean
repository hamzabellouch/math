import OAI.Combinatorics.ContingencyTables.Machines.BinaryExchangeProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseIntegerProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionFactorialApplication

namespace OAI

/-! # Computing the companion's retained small-cell capacities

The program scans the rectangular cell list determined by the two
margin-list lengths, then tests the binary cell bound against W. It
does not enumerate up to the numeric value of a capacity.
-/

namespace ContingencyTables.CompanionCellCatalog

open MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms

abbrev Input := ((List ℕ×List ℕ)×MatrixCode)×ℕ

def entry (z : Input×(ℕ×ℕ)) : ℕ := matrixEntry (z.1.1.2,z.2)

def entryRealizer : Realizer entry :=
  composition (pair (composition (composition first first) second) second) matrixEntryRealizer

lemma polynomial_entry : PolynomialTime entryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) polynomial_second) polynomial_matrixEntry

def retainedTest (z : Input×(ℕ×ℕ)) : Bool := decide (entry z<z.1.2)

def retainedTestRealizer : Realizer retainedTest :=
  composition (pair entryRealizer (composition first second)) less

lemma polynomial_retainedTest : PolynomialTime retainedTestRealizer :=
  polynomial_composition (polynomial_pair polynomial_entry
    (polynomial_composition polynomial_first polynomial_second)) polynomial_less

def catalog (z : Input) : List (ℕ×ℕ) :=
  (cellPairs z.1.1).filter (fun a => retainedTest (z,a))

def catalogRealizer : Realizer catalog :=
  composition (pair identity
    (composition (composition first first) cellPairsRealizer)) (filterWith retainedTestRealizer)

theorem polynomial_catalog : PolynomialTime catalogRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_cellPairs)) (polynomial_filterWith polynomial_retainedTest)

def capacities (z : Input) : List ℕ := (catalog z).map (fun a => entry (z,a))

def capacitiesRealizer : Realizer capacities :=
  composition (pair identity catalogRealizer) (mapWith entryRealizer)

theorem polynomial_capacities : PolynomialTime capacitiesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_catalog)
    (polynomial_mapWith polynomial_entry)

lemma catalog_nodup (z : Input) : (catalog z).Nodup :=
  (cellPairs_nodup z.1.1.1 z.1.1.2).filter _

noncomputable section
open CompanionFactorialApplication
open scoped Classical
variable {m n : ℕ}

def input (A : Instance (Fin m) (Fin n)) : Input :=
  (((List.ofFn (fun i => (A.r i).toNat),List.ofFn (fun j => (A.c j).toNat)),
    matrixCode A.b),A.W)

lemma small_iff_bound (A : Instance (Fin m) (Fin n)) (i : Fin m) (j : Fin n) :
    A.small i j=true ↔ A.b i j<A.W := by
  constructor
  · exact A.hsmall i j
  · intro hb
    cases hs : A.small i j
    · have hh := (A.hlarge i j hs).1
      omega
    · rfl

lemma entry_input (A : Instance (Fin m) (Fin n)) (i : Fin m) (j : Fin n) :
    entry (input A,(i.val,j.val))=A.b i j := matrixEntry_code A.b i j

lemma mem_catalog_input (A : Instance (Fin m) (Fin n)) (ij : ℕ×ℕ) :
    ij∈catalog (input A) ↔ ∃ a : SmallCell A,(a.val.1.val,a.val.2.val)=ij := by
  rw [catalog,List.mem_filter]
  change (ij∈cellPairs (List.ofFn (fun i => (A.r i).toNat),
    List.ofFn (fun j => (A.c j).toNat)) ∧ retainedTest (input A,ij)=true) ↔ _
  rw [mem_cellPairs]
  simp only [List.length_ofFn]
  constructor
  · rintro ⟨⟨hi,hj⟩,hb⟩
    let i : Fin m := ⟨ij.1,hi⟩
    let j : Fin n := ⟨ij.2,hj⟩
    have he : A.b i j<A.W := by
      have hh : entry (input A,(i.val,j.val))<A.W := of_decide_eq_true hb
      rwa [entry_input] at hh
    have hs : A.small i j=true := (small_iff_bound A i j).mpr he
    exact ⟨⟨(i,j),hs⟩,rfl⟩
  · rintro ⟨a,rfl⟩
    refine ⟨⟨a.val.1.isLt,a.val.2.isLt⟩,?_⟩
    apply decide_eq_true
    change entry (input A,(a.val.1.val,a.val.2.val))<A.W
    rw [entry_input]
    exact A.hsmall _ _ a.property

def catalogCell (A : Instance (Fin m) (Fin n)) (i : Fin (catalog (input A)).length) : SmallCell A :=
  Classical.choose ((mem_catalog_input A ((catalog (input A))[i.val])).mp
    (List.getElem_mem i.isLt))

lemma catalogCell_coordinates (A : Instance (Fin m) (Fin n))
    (i : Fin (catalog (input A)).length) :
    ((catalogCell A i).val.1.val,(catalogCell A i).val.2.val)=(catalog (input A))[i.val] :=
  Classical.choose_spec ((mem_catalog_input A ((catalog (input A))[i.val])).mp
    (List.getElem_mem i.isLt))

lemma catalogCell_bijective (A : Instance (Fin m) (Fin n)) :
    Function.Bijective (catalogCell A) := by
  constructor
  · intro i j h
    have he := congrArg (fun a : SmallCell A => (a.val.1.val,a.val.2.val)) h
    rw [catalogCell_coordinates,catalogCell_coordinates] at he
    exact Fin.ext ((catalog_nodup (input A)).getElem_inj_iff.mp he)
  · intro a
    have hm : (a.val.1.val,a.val.2.val)∈catalog (input A) :=
      (mem_catalog_input A _).mpr ⟨a,rfl⟩
    obtain ⟨i,hi,hval⟩ := List.mem_iff_getElem.mp hm
    refine ⟨⟨i,hi⟩,?_⟩
    have he := (catalogCell_coordinates A ⟨i,hi⟩).trans hval
    apply Subtype.ext
    exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

def cellEquiv (A : Instance (Fin m) (Fin n)) :
    Fin (catalog (input A)).length ≃ SmallCell A :=
  Equiv.ofBijective (catalogCell A) (catalogCell_bijective A)

lemma capacities_eq (A : Instance (Fin m) (Fin n)) :
    capacities (input A)=List.ofFn (fun i => A.b ((cellEquiv A) i).val.1 ((cellEquiv A) i).val.2) := by
  apply List.ext_getElem
  · simp only [capacities,List.length_map,List.length_ofFn]
  · intro i hi hj
    have hi' : i<(catalog (input A)).length := by simpa only [List.length_ofFn] using hj
    simp only [capacities,List.getElem_map,List.getElem_ofFn]
    have he := catalogCell_coordinates A ⟨i,hi'⟩
    change entry (input A,(catalog (input A))[i]'hi')=
      A.b (catalogCell A ⟨i,hi'⟩).val.1 (catalogCell A ⟨i,hi'⟩).val.2
    rw [←he]
    exact entry_input A _ _

end
end ContingencyTables.CompanionCellCatalog

end OAI
