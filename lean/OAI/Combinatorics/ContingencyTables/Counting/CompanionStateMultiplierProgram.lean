import OAI.Combinatorics.ContingencyTables.Counting.CompanionMultiplierMatrixProgram

namespace OAI

/-! # Reading the multiplier of an actual encoded chain state

The at most quadratic list of labelled defect types is searched using
the proved occupancy test. Uniqueness of defect labels identifies the
selected matrix entry with the mathematical chain multiplier.
-/

namespace ContingencyTables.CompanionStateMultiplierProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms
open CompanionChainValidator CompanionPhaseCounts CompanionMultiplierMatrixProgram

def coordinates (z : ValidatorInput) : List ℕ := z.1.map Prod.fst
def coordinatesRealizer : Realizer coordinates := composition first (map first)
lemma polynomial_coordinates : PolynomialTime coordinatesRealizer :=
  polynomial_composition polynomial_first (polynomial_map polynomial_first)

def candidates (z : ValidatorInput) : List (ℕ × ℕ) := cellPairs (coordinates z,coordinates z)
def candidatesRealizer : Realizer candidates :=
  composition (pair coordinatesRealizer coordinatesRealizer) cellPairsRealizer
lemma polynomial_candidates : PolynomialTime candidatesRealizer :=
  polynomial_composition (polynomial_pair polynomial_coordinates polynomial_coordinates) polynomial_cellPairs

def found (z : ValidatorInput) : List (ℕ × ℕ) :=
  (candidates z).filter (fun st => pairedDefectTest (z,st))
def foundRealizer : Realizer found :=
  composition (pair identity candidatesRealizer) (filterWith pairedDefectTestRealizer)
lemma polynomial_found : PolynomialTime foundRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_candidates)
    (polynomial_filterWith polynomial_pairedDefectTest)

abbrev Input := FractionMatrix × ValidatorInput

def noDefect (z : Input) : Bool := (found z.2).isEmpty
def noDefectRealizer : Realizer noDefect := composition (composition second foundRealizer) isEmpty
lemma polynomial_noDefect : PolynomialTime noDefectRealizer :=
  polynomial_composition (polynomial_composition polynomial_second polynomial_found) polynomial_isEmpty

def readDefect (z : Input) : TreeFraction.Fraction := readEntry (z.1,(found z.2).getD 0 (0,0))
def readDefectRealizer : Realizer readDefect :=
  composition (f := fun z : Input => (z.1,(found z.2).getD 0 (0,0))) (g := readEntry)
    (pair first (composition (pair (composition second foundRealizer) (constant 0))
      (getDFast (0,0)))) readEntryRealizer
lemma polynomial_readDefect : PolynomialTime readDefectRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_found) (polynomial_constant 0))
      (polynomial_getDFast (0,0)))) polynomial_readEntry

def output (z : Input) : TreeFraction.Fraction := if noDefect z then (1,1) else readDefect z
def outputRealizer : Realizer output := choose noDefectRealizer (constant (1,1)) readDefectRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_choose polynomial_noDefect (polynomial_constant (1,1)) polynomial_readDefect

noncomputable section
open CompanionFactorialApplication CompanionArithmeticProposal CompanionOrderedProposal
open CommonBasesFPRAS TwoLiftStates
open scoped Classical
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p m : ℕ} (g : Fin p ≃ Labels A) (e : (Labels A × Bool) ≃ Fin m)

lemma candidates_mem (S : Set (Labels A × Bool)) (ij : ℕ × ℕ) :
    ij ∈ candidates (orderedCatalog A g e,encodeSet e S) ↔ ij.1 < p ∧ ij.2 < p := by
  rcases ij with ⟨i,j⟩
  unfold candidates
  rw [mem_cellPairs]
  simp only [coordinates,orderedCatalog,List.length_map,List.length_ofFn]

lemma found_mem (S : Set (Labels A × Bool)) (ij : ℕ × ℕ) :
    ij ∈ found (orderedCatalog A g e,encodeSet e S) ↔
      ∃ (i j : Fin p), (i.val,j.val)=ij ∧ DefectState pairs (pair (g i)) (pair (g j)) S := by
  rw [found,List.mem_filter,candidates_mem]
  constructor
  · rintro ⟨⟨hi,hj⟩,ht⟩
    refine ⟨⟨ij.1,hi⟩,⟨ij.2,hj⟩,rfl,?_⟩
    exact (defectTest_ordered A g e S _ _).mp ht
  · rintro ⟨i,j,hij,ht⟩
    cases hij
    exact ⟨⟨i.isLt,j.isLt⟩,(defectTest_ordered A g e S i j).mpr ht⟩

lemma found_exists (S : Set (Labels A × Bool)) :
    found (orderedCatalog A g e,encodeSet e S) ≠ [] ↔
      ∃ a b,DefectState pairs a b S := by
  constructor
  · intro hn
    obtain ⟨ij,hij⟩ := List.exists_mem_of_ne_nil _ hn
    obtain ⟨i,j,_,hd⟩ := (found_mem A g e S ij).mp hij
    exact ⟨pair (g i),pair (g j),hd⟩
  · rintro ⟨a,b,hd⟩ hn
    obtain ⟨u,_,hu⟩ := List.mem_map.mp hd.1
    obtain ⟨v,_,hv⟩ := List.mem_map.mp hd.2.1
    have hm : ((g.symm u).val,(g.symm v).val) ∈ found (orderedCatalog A g e,encodeSet e S) := by
      apply (found_mem A g e S _).mpr
      refine ⟨g.symm u,g.symm v,rfl,?_⟩
      simpa only [Equiv.apply_symm_apply,hu,hv] using hd
    simp only [hn,List.not_mem_nil] at hm

theorem output_code (S : Set (Labels A × Bool)) (w : Fin p → Fin p → TreeFraction.Fraction) :
    TreeFraction.val (output (CompanionMultiplierMatrixProgram.matrixCode w,
      (orderedCatalog A g e,encodeSet e S)))=
        rationalMultiplier pairs
          (fun a b => TreeFraction.val (w (g.symm a.1.1) (g.symm b.1.1))) S := by
  by_cases h : ∃ a b,DefectState pairs a b S
  · have hn := (found_exists A g e S).mpr h
    have hm : (found (orderedCatalog A g e,encodeSet e S)).getD 0 (0,0) ∈
        found (orderedCatalog A g e,encodeSet e S) := by
      cases hl : found (orderedCatalog A g e,encodeSet e S) with
      | nil => exact (hn hl).elim
      | cons a as => simp only [List.getD_cons_zero,List.mem_cons,true_or]
    obtain ⟨i,j,hij,hd⟩ := (found_mem A g e S _).mp hm
    have he := hd.unique h.choose_spec.choose_spec
    unfold output noDefect readDefect
    have heNonempty : (found (orderedCatalog A g e,encodeSet e S)).isEmpty=false := by
      cases hl : found (orderedCatalog A g e,encodeSet e S) with
      | nil => exact (hn hl).elim
      | cons a as => rfl
    rw [heNonempty]
    simp only [Bool.false_eq_true,ite_false]
    rw [←hij,readEntry_code]
    have hi : g i=h.choose.1.1 := congrArg (fun a => a.1.1) he.1
    have hj : g j=h.choose_spec.choose.1.1 := congrArg (fun a => a.1.1) he.2
    have hi' : i=g.symm h.choose.1.1 := by
      simpa only [Equiv.symm_apply_apply] using congrArg g.symm hi
    have hj' : j=g.symm h.choose_spec.choose.1.1 := by
      simpa only [Equiv.symm_apply_apply] using congrArg g.symm hj
    rw [rationalMultiplier,dite_eq_left h]
    rw [←hi',←hj']
  · have hn : found (orderedCatalog A g e,encodeSet e S)=[] := by
      by_contra hn
      exact h ((found_exists A g e S).mp hn)
    simp only [output,noDefect,hn,List.isEmpty_nil,ite_true,TreeFraction.val,
      Nat.cast_one,div_one,rationalMultiplier,dite_eq_right h]

end
end ContingencyTables.CompanionStateMultiplierProgram

end OAI
