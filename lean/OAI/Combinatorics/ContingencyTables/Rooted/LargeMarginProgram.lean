import OAI.Combinatorics.ContingencyTables.Sampling.PaddedResidualProgram
import OAI.Combinatorics.ContingencyTables.Sampling.SmallProfileValidator
import Mathlib.Data.List.NodupEquivFin

namespace OAI

/-! # Computing the large rectangle and its padded margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def largeIndexTest (z : (ℕ×List ℕ)×ℕ) : Bool :=
  decide (z.1.1≤z.1.2.getD z.2 0)

def largeIndexTestRealizer : Realizer largeIndexTest :=
  composition (pair (composition first first)
    (composition (pair (composition first second) second) (getDFast 0))) leNat

theorem polynomial_largeIndexTest : PolynomialTime largeIndexTestRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      (polynomial_getDFast 0))) polynomial_leNat

def largeIndices (z : ℕ×List ℕ) : List ℕ :=
  (List.range z.2.length).filter (fun i => largeIndexTest (z,i))

def largeIndicesRealizer : Realizer largeIndices :=
  composition (pair identity (composition (composition second listLength) range))
    (filterWith largeIndexTestRealizer)

theorem polynomial_largeIndices : PolynomialTime largeIndicesRealizer := by
  have hr : PolynomialTime (composition (composition
      (second (A := ℕ) (B := List ℕ)) listLength) range) := by
    apply polynomial_boundedRange (polynomial_composition polynomial_second polynomial_listLength)
      Polynomial.X
    intro z
    simpa only [Function.comp_apply,Polynomial.eval_X] using
      (list_length_le_weight z.2).trans (by rw [weight_prod]; omega)
  exact polynomial_composition (polynomial_pair polynomial_identity hr)
    (polynomial_filterWith polynomial_largeIndexTest)

def selectList {A : Type} (a : A) (z : List ℕ×List A) : List A :=
  z.1.map (fun i => z.2.getD i a)

def selectListRealizer {A : Type} [Codec A] (a : A) : Realizer (selectList a) :=
  composition (pair second first) (mapWith (getDFast a))

theorem polynomial_selectList {A : Type} [Codec A] (a : A) :
    PolynomialTime (selectListRealizer a) :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_mapWith (polynomial_getDFast a))

def largePaddedMargins (row : Bool) (z : PaddingData) : List ℕ :=
  selectList 0 (largeIndices (z.1.2,marginList row z.1),paddedMargins row z)

def largePaddedMarginsRealizer (row : Bool) : Realizer (largePaddedMargins row) :=
  composition (pair
    (composition (pair (composition first second)
      (composition first (marginListRealizer row))) largeIndicesRealizer)
    (paddedMarginsRealizer row)) (selectListRealizer 0)

theorem polynomial_largePaddedMargins (row : Bool) :
    PolynomialTime (largePaddedMarginsRealizer row) :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition polynomial_first (polynomial_marginList row)))
      polynomial_largeIndices) (polynomial_paddedMargins row)) (polynomial_selectList 0)

def profilePaddedMargins (row : Bool) (z : ProfileCheckData×ℕ) : List ℕ :=
  largePaddedMargins row
    (((((z.1.1.1.1,if row then z.1.1.1.2.1 else complementValues (z.1.2,z.1.1.1.2.2)),
      z.1.1.2),z.1.2)),z.2)

def profilePaddedMarginsRealizer (row : Bool) : Realizer (profilePaddedMargins row) :=
  composition (pair (composition first (profileLineData row)) second)
    (largePaddedMarginsRealizer row)

theorem polynomial_profilePaddedMargins (row : Bool) :
    PolynomialTime (profilePaddedMarginsRealizer row) :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first (polynomial_profileLineData row)) polynomial_second)
    (polynomial_largePaddedMargins row)

lemma mem_largeIndices (U : ℕ) (r : List ℕ) (i : ℕ) :
    i∈largeIndices (U,r) ↔ i<r.length ∧ U≤r.getD i 0 := by
  simp only [largeIndices,List.mem_filter,List.mem_range,largeIndexTest,decide_eq_true_eq]

lemma largeIndices_nodup (U : ℕ) (r : List ℕ) : (largeIndices (U,r)).Nodup :=
  (List.nodup_range (n := r.length)).filter _

lemma largePaddedMargins_eq (row : Bool) (z : PaddingData) :
    largePaddedMargins row z=
      (largeIndices (z.1.2,marginList row z.1)).map (fun i => paddedMarginAt row (z,i)) := by
  change (largeIndices (z.1.2,marginList row z.1)).map
    (fun i => (paddedMargins row z).getD i 0)=_
  apply List.map_congr_left
  intro i hi
  have hi' := (mem_largeIndices _ _ _).mp hi
  rw [List.getD_eq_getElem (l := paddedMargins row z) (n := i) (d := 0)
    (by simpa only [paddedMargins,List.length_map,List.length_range] using hi'.1)]
  simp only [paddedMargins,List.getElem_map,List.getElem_range]

end ContingencyTables.ProfilePrograms

end OAI
