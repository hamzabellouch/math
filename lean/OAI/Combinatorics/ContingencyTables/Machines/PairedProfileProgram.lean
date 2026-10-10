import OAI.Combinatorics.ContingencyTables.Machines.NaturalBlockProgram
import OAI.Combinatorics.ContingencyTables.Machines.PairedCatalogProgram

namespace OAI

/-! # Reading the two cell counts from the actual paired code

The block widths come from the stored capacity list. Each count scans
only supplied code entries and clips them to one, including on malformed
input. No numeric capacity controls an unbounded allocation.
-/

namespace ContingencyTables.PairedProfileProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

abbrev ReadInput := (List ℕ × Bool) × (ℕ × ℕ)

def sideValue (z : ReadInput) : ℕ :=
  min (z.1.1.getD (if z.1.2 then z.2.2 else z.2.1) 0) 1
def sideValueRealizer : Realizer sideValue :=
  composition (f := fun z : ReadInput =>
      (z.1.1.getD (if z.1.2 then z.2.2 else z.2.1) 0,1))
    (g := fun p : ℕ × ℕ => min p.1 p.2)
    (pair (composition (pair (composition first first)
      (choose (composition first second) (composition second second)
        (composition second first))) (getDFast 0)) (constant 1)) minimum
lemma polynomial_sideValue : PolynomialTime sideValueRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_choose (polynomial_composition polynomial_first polynomial_second)
        (polynomial_composition polynomial_second polynomial_second)
        (polynomial_composition polynomial_second polynomial_first))) (polynomial_getDFast 0))
    (polynomial_constant 1)) polynomial_minimum

def sideEntries (z : List ℕ × Bool) : List ℕ :=
  (PairedCatalogProgram.catalog z.1).map (fun p => sideValue (z,p))
def sideEntriesRealizer : Realizer sideEntries :=
  composition (pair identity (composition first PairedCatalogProgram.catalogRealizer))
    (mapWith sideValueRealizer)
lemma polynomial_sideEntries : PolynomialTime sideEntriesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first PairedCatalogProgram.polynomial_catalog))
    (polynomial_mapWith polynomial_sideValue)

def sideCount (z : List ℕ × Bool) : ℕ := (sideEntries z).sum
def sideCountRealizer : Realizer sideCount := composition sideEntriesRealizer listSum
lemma polynomial_sideCount : PolynomialTime sideCountRealizer :=
  polynomial_composition polynomial_sideEntries polynomial_listSum

lemma sideCount_le (xs : List ℕ) (side : Bool) : sideCount (xs,side) ≤ xs.length := by
  have hs : (sideEntries (xs,side)).sum ≤ (sideEntries (xs,side)).length := by
    simpa using (List.sum_le_length_nsmul (sideEntries (xs,side)) 1 (by
      intro a ha
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
      exact Nat.min_le_right _ _))
  exact hs.trans (by
    simp only [sideEntries,PairedCatalogProgram.catalog,List.length_map,List.length_range]
    exact Nat.div_le_self _ _)

abbrev Input := List ℕ × List ℕ

def width (n : ℕ) : ℕ := 2*n
def widthRealizer : Realizer width :=
  composition (f := fun n : ℕ => (2,n)) (g := fun p : ℕ × ℕ => p.1*p.2)
    (pair (constant 2) identity) multiply
lemma polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_identity)
    polynomial_multiply

def rows (z : Input) : List (List ℕ) :=
  NaturalBlockProgram.blocks (z.1.map width,z.2)
def rowsRealizer : Realizer rows :=
  composition (pair (composition first (map widthRealizer)) second)
    NaturalBlockProgram.blocksRealizer
lemma polynomial_rows : PolynomialTime rowsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first (polynomial_map polynomial_width)) polynomial_second)
    NaturalBlockProgram.polynomial_blocks

def counts (xs : List ℕ) : ℕ × ℕ := (sideCount (xs,false),sideCount (xs,true))
def countsRealizer : Realizer counts :=
  pair (composition (f := fun xs : List ℕ => (xs,false)) (g := sideCount)
    (pair identity (constant false)) sideCountRealizer)
    (composition (f := fun xs : List ℕ => (xs,true)) (g := sideCount)
      (pair identity (constant true)) sideCountRealizer)
lemma polynomial_counts : PolynomialTime countsRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant false))
      polynomial_sideCount)
    (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant true))
      polynomial_sideCount)

def profileRows (z : Input) : List (ℕ × ℕ) := (rows z).map counts
def profileRowsRealizer : Realizer profileRows := composition rowsRealizer (map countsRealizer)
theorem polynomial_profileRows : PolynomialTime profileRowsRealizer :=
  polynomial_composition polynomial_rows (polynomial_map polynomial_counts)

def interleave : List (ℕ × ℕ) → List ℕ
  | [] => []
  | p :: ps => p.1 :: p.2 :: interleave ps

lemma interleave_length (xs : List (ℕ × ℕ)) : (interleave xs).length=2*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [interleave,List.length_cons,ih]; omega

lemma interleave_get_even (xs : List (ℕ × ℕ)) (i : ℕ) (hi : i < xs.length) :
    (interleave xs)[2*i]'(by rw [interleave_length]; omega)=xs[i].1 := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [interleave,Nat.mul_succ,List.getElem_cons_succ] using
        ih i (Nat.lt_of_succ_lt_succ hi)

lemma interleave_get_odd (xs : List (ℕ × ℕ)) (i : ℕ) (hi : i < xs.length) :
    (interleave xs)[2*i+1]'(by rw [interleave_length]; omega)=xs[i].2 := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [interleave,Nat.mul_succ,List.getElem_cons_succ,Nat.add_assoc] using
        ih i (Nat.lt_of_succ_lt_succ hi)

lemma sideEntries_interleave (xs : List (ℕ × ℕ)) (side : Bool) :
    sideEntries (interleave xs,side)=
      xs.map (fun p => min (if side then p.2 else p.1) 1) := by
  apply List.ext_getElem
  · simp only [sideEntries,PairedCatalogProgram.catalog,List.length_map,List.length_range,
      interleave_length,Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  · intro i hi _
    have hii : i < xs.length := by
      simpa only [sideEntries,PairedCatalogProgram.catalog,List.length_map,List.length_range,
        interleave_length,Nat.mul_div_cancel_left _ (by decide : 0 < 2)] using hi
    simp only [sideEntries,PairedCatalogProgram.catalog,List.getElem_map,List.getElem_range,
      sideValue,PairedCatalogProgram.indexPair]
    cases side with
    | false =>
      have hidx : 2*i < (interleave xs).length := by rw [interleave_length]; omega
      simp only [Bool.false_eq_true,ite_false,List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hidx,Option.getD_some,interleave_get_even xs i hii]
    | true =>
      have hidx : 2*i+1 < (interleave xs).length := by rw [interleave_length]; omega
      simp only [ite_true,List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hidx,Option.getD_some,interleave_get_odd xs i hii]

lemma interleave_flatMap (xs : List (ℕ × ℕ)) :
    interleave xs=xs.flatMap (fun p => [p.1,p.2]) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    change p.1 :: p.2 :: interleave xs=p.1 :: p.2 :: xs.flatMap (fun p => [p.1,p.2])
    rw [ih]

end ContingencyTables.PairedProfileProgram

end OAI
