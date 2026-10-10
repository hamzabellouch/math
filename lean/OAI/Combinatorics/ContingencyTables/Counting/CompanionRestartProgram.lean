import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartStageProgram
import OAI.Combinatorics.ContingencyTables.Machines.DependentWordProgram

namespace OAI

/-! # Executed restart stages with disjoint variable-width words

The supplied stage list determines the number of iterations. The current
encoded profile is bounded by the original profile length after every stage.
-/
namespace ContingencyTables.CompanionRestartProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial DensePrograms
open CompanionMultiplierMatrixProgram

abbrev Stage := CompanionPhaseContextProgram.Input × FractionMatrix
abbrev Input := (List Stage × List ℕ) × List Bool
abbrev State := Input × List ℕ

def request (z : Input × ℕ) : CompanionRestartStageProgram.Request :=
  (z.1.1.1.getD z.2 default,z.1.1.2)
def requestRealizer : Realizer request :=
  pair (composition (f := fun z : Input×ℕ => (z.1.1.1,z.2))
    (g := fun p : List Stage×ℕ => p.1.getD p.2 default)
    (pair (composition (composition first first) first) second) (getDFast default))
    (composition (composition first first) second)
lemma polynomial_request : PolynomialTime requestRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_second) (polynomial_getDFast default))
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)

def indices (z : Input) : List ℕ := List.range z.1.1.length
def indicesRealizer : Realizer indices :=
  composition (composition (composition first first) listLength) range
lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition
      polynomial_first polynomial_first) polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

def indexedWidth (z : Input×ℕ) : ℕ := CompanionRestartStageProgram.width (request z)
def indexedWidthRealizer : Realizer indexedWidth :=
  composition (f := request) (g := CompanionRestartStageProgram.width)
    requestRealizer CompanionRestartStageProgram.widthRealizer
lemma polynomial_indexedWidth : PolynomialTime indexedWidthRealizer :=
  polynomial_composition polynomial_request CompanionRestartStageProgram.polynomial_width

def widths (z : Input) : List ℕ := (indices z).map (fun i => indexedWidth (z,i))
def widthsRealizer : Realizer widths :=
  composition (pair identity indicesRealizer) (mapWith indexedWidthRealizer)
lemma polynomial_widths : PolynomialTime widthsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_indexedWidth)

def stageWord (z : Input×ℕ) : List Bool := dependentChunk ((widths z.1,z.1.2),z.2)
def stageWordRealizer : Realizer stageWord :=
  composition (f := fun z : Input×ℕ => ((widths z.1,z.1.2),z.2))
    (g := dependentChunk)
    (pair (pair (composition (f := fun z : Input×ℕ => z.1) (g := widths) first widthsRealizer)
      (composition first second)) second) dependentChunkRealizer
lemma polynomial_stageWord : PolynomialTime stageWordRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_widths)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_second)
    polynomial_dependentChunk

def stageInput (z : ℕ×State) : CompanionRestartStageProgram.Input :=
  ((z.2.1.1.1.getD z.1 default,z.2.2),stageWord (z.2.1,z.1))
def stageInputRealizer : Realizer stageInput := by
  let selected : Realizer (fun z : ℕ×State => z.2.1.1.1.getD z.1 (default : Stage)) :=
    composition (f := fun z : ℕ×State => (z.2.1.1.1,z.1))
      (g := fun p : List Stage×ℕ => p.1.getD p.2 default)
      (pair (composition (composition (composition second first) first) first) first) (getDFast default)
  exact pair (pair selected (composition second second))
    (composition (f := fun z : ℕ×State => (z.2.1,z.1)) (g := stageWord)
      (pair (composition second first) first) stageWordRealizer)
lemma polynomial_stageInput : PolynomialTime stageInputRealizer := by
  unfold stageInputRealizer
  apply polynomial_pair
  · apply polynomial_pair
    · exact polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition (polynomial_composition
          polynomial_second polynomial_first) polynomial_first) polynomial_first)
        polynomial_first) (polynomial_getDFast default)
    · exact polynomial_composition polynomial_second polynomial_second
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_first) polynomial_first) polynomial_stageWord

def candidate (z : ℕ×State) : List ℕ := CompanionRestartStageProgram.output (stageInput z)
def candidateRealizer : Realizer candidate :=
  composition (f := stageInput) (g := CompanionRestartStageProgram.output)
    stageInputRealizer CompanionRestartStageProgram.outputRealizer
lemma polynomial_candidate : PolynomialTime candidateRealizer :=
  polynomial_composition polynomial_stageInput CompanionRestartStageProgram.polynomial_output

def bound (z : ℕ×State) : ℕ := z.2.1.1.2.length
def boundRealizer : Realizer bound :=
  composition (composition (composition (composition second first) first) second) listLength
lemma polynomial_bound : PolynomialTime boundRealizer :=
  polynomial_composition (polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_second polynomial_first) polynomial_first) polynomial_second)
    polynomial_listLength

attribute [local irreducible] candidate

def next (z : ℕ×State) : List ℕ := ProfilePrograms.capView ((bound z,1),candidate z)
def nextRealizer : Realizer next :=
  composition (f := fun z : ℕ×State => ((bound z,1),candidate z)) (g := ProfilePrograms.capView)
    (pair (pair boundRealizer (constant 1)) candidateRealizer) ProfilePrograms.capViewRealizer
lemma polynomial_next : PolynomialTime nextRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair polynomial_bound (polynomial_constant 1))
    polynomial_candidate) ProfilePrograms.polynomial_capView

def advance (z : ℕ×State) : State := (z.2.1,next z)
def advanceRealizer : Realizer advance := pair (composition second first) nextRealizer
lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first) polynomial_next

lemma advance_weight (i : ℕ) (state : State) (S : ℕ) (hs : weight state.1 ≤ S) :
    weight (advance (i,state)) ≤ 10*(S+1) := by
  have hb : state.1.1.2.length ≤ S := (list_length_le_weight _).trans
    ((weight_snd state.1.1).trans ((weight_fst state.1).trans hs))
  have hn := ProfilePrograms.capView_weight state.1.1.2.length 1 (candidate (i,state))
  change weight (next (i,state)) ≤ _ at hn
  norm_num only [Nat.size_one] at hn
  change weight (state.1,next (i,state)) ≤ _
  rw [weight_prod]
  omega

def walk (z : State×List ℕ) : State := z.2.foldl (fun state i => advance (i,state)) z.1
def walkRealizer : Realizer walk := composition (pair second first) (fold advanceRealizer)

lemma fold_fixed (is : List ℕ) (state : State) :
    (is.foldl (fun state i => advance (i,state)) state).1=state.1 := by
  induction is generalizing state with
  | nil => rfl
  | cons i is ih => exact ih _

lemma fold_weight (is : List ℕ) (state : State) (S : ℕ) (hs : weight state ≤ S) :
    weight (is.foldl (fun state i => advance (i,state)) state) ≤ 10*(S+1) := by
  induction is using List.reverseRecOn with
  | nil => simpa using hs.trans (by omega : S ≤ 10*(S+1))
  | append_singleton is i _ =>
    rw [List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    apply advance_weight
    rw [fold_fixed]
    exact (weight_fst state).trans hs

theorem polynomial_walk : PolynomialTime walkRealizer := by
  apply polynomial_composition (polynomial_pair polynomial_second polynomial_first)
  apply polynomial_fold polynomial_advance (10*(X+1))
  intro is state pre post _
  simp only [eval_mul,eval_ofNat,eval_add,eval_X,eval_one]
  exact fold_weight pre state (weight (is,state)) (weight_snd (is,state))

def output (z : Input) : List ℕ := (walk ((z,z.1.2),indices z)).2
def outputRealizer : Realizer output :=
  composition (f := fun z : Input => ((z,z.1.2),indices z))
    (g := fun z : State×List ℕ => (walk z).2)
    (pair (pair identity (composition first second)) indicesRealizer)
    (composition (f := walk) (g := Prod.snd) walkRealizer second)
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_second)) polynomial_indices)
    (polynomial_composition polynomial_walk polynomial_second)

end ContingencyTables.CompanionRestartProgram

end OAI
