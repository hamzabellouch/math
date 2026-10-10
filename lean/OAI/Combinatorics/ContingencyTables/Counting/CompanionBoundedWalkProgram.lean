import OAI.Combinatorics.ContingencyTables.Counting.CompanionMetropolisWordProgram
import OAI.Combinatorics.ContingencyTables.Transport.BoundedProfileWalk

namespace OAI

/-! # Polynomial iteration of the physical companion transition

Clipping is redundant on the encoded binary chain states. It gives a
uniform bound on malformed inputs, so repeated calls remain polynomial.
-/

namespace ContingencyTables.CompanionBoundedWalkProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

abbrev Fixed := (CompanionMetropolisProgram.Frame × ℕ) × List ℕ
abbrev State := Fixed × List ℕ

def transitionInput (z : List Bool × State) : CompanionMetropolisWordProgram.Input :=
  ((z.2.1.1,z.2.2),z.1)
def transitionInputRealizer : Realizer transitionInput :=
  pair (pair (composition (composition second first) first) (composition second second)) first
lemma polynomial_transitionInput : PolynomialTime transitionInputRealizer :=
  polynomial_pair (polynomial_pair (by tree_poly) (polynomial_composition polynomial_second polynomial_second))
    polynomial_first

def candidate (z : List Bool × State) : List ℕ := CompanionMetropolisWordProgram.output (transitionInput z)
def candidateRealizer : Realizer candidate :=
  composition (f := transitionInput) (g := CompanionMetropolisWordProgram.output)
    transitionInputRealizer CompanionMetropolisWordProgram.outputRealizer
lemma polynomial_candidate : PolynomialTime candidateRealizer :=
  polynomial_composition polynomial_transitionInput CompanionMetropolisWordProgram.polynomial_output

def bound (z : List Bool × State) : ℕ := z.2.1.2.length
def boundRealizer : Realizer bound :=
  composition (composition (composition second first) second) listLength
lemma polynomial_bound : PolynomialTime boundRealizer :=
  polynomial_composition (polynomial_composition (polynomial_composition
    polynomial_second polynomial_first) polynomial_second) polynomial_listLength

attribute [local irreducible] candidate

def next (z : List Bool × State) : List ℕ := ProfilePrograms.capView ((bound z,1),candidate z)
def nextRealizer : Realizer next :=
  composition (f := fun z : List Bool × State => ((bound z,1),candidate z))
    (g := ProfilePrograms.capView) (pair (pair boundRealizer (constant 1)) candidateRealizer)
    ProfilePrograms.capViewRealizer
lemma polynomial_next : PolynomialTime nextRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair polynomial_bound (polynomial_constant 1))
    polynomial_candidate) ProfilePrograms.polynomial_capView

def advance (z : List Bool × State) : State := (z.2.1,next z)
def advanceRealizer : Realizer advance := pair (composition second first) nextRealizer
lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first) polynomial_next

lemma advance_fixed (word : List Bool) (state : State) : (advance (word,state)).1=state.1 := rfl

lemma advance_weight (word : List Bool) (state : State) (S : ℕ) (hs : weight state.1 ≤ S) :
    weight (advance (word,state)) ≤ 10*(S+1) := by
  have hb : state.1.2.length ≤ S :=
    (list_length_le_weight _).trans ((weight_snd state.1).trans hs)
  have hn := ProfilePrograms.capView_weight state.1.2.length 1 (candidate (word,state))
  change weight (next (word,state)) ≤ _ at hn
  norm_num only [Nat.size_one] at hn
  change weight (state.1,next (word,state)) ≤ _
  rw [weight_prod]
  omega

def walk (z : State × List (List Bool)) : State :=
  z.2.foldl (fun state bits => advance (bits,state)) z.1
def walkRealizer : Realizer walk := composition (pair second first) (fold advanceRealizer)

lemma fold_fixed (words : List (List Bool)) (state : State) :
    (words.foldl (fun state bits => advance (bits,state)) state).1=state.1 := by
  induction words generalizing state with
  | nil => rfl
  | cons word words ih => exact ih _

lemma fold_weight (words : List (List Bool)) (state : State) (S : ℕ) (hs : weight state ≤ S) :
    weight (words.foldl (fun state bits => advance (bits,state)) state) ≤ 10*(S+1) := by
  induction words using List.reverseRecOn with
  | nil => simpa using hs.trans (by omega : S ≤ 10*(S+1))
  | append_singleton words word _ =>
    rw [List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    apply advance_weight
    rw [fold_fixed]
    exact (weight_fst state).trans hs

theorem polynomial_walk : PolynomialTime walkRealizer := by
  apply polynomial_composition (polynomial_pair polynomial_second polynomial_first)
  apply polynomial_fold polynomial_advance (10*(X+1))
  intro words state pre post _
  simp only [eval_mul,eval_ofNat,eval_add,eval_X,eval_one]
  exact fold_weight pre state (weight (words,state)) (weight_snd (words,state))

abbrev RecordState := State × List (List ℕ)

def recordAdvance (z : List Bool × RecordState) : RecordState :=
  let nextState := advance (z.1,z.2.1)
  (nextState,nextState.2::z.2.2)
def recordAdvanceRealizer : Realizer recordAdvance := by
  let nxt : Realizer (fun z : List Bool × RecordState => advance (z.1,z.2.1)) :=
    composition (f := fun z : List Bool × RecordState => (z.1,z.2.1)) (g := advance)
      (pair first (composition second first)) advanceRealizer
  exact pair nxt (composition (pair (composition nxt second) (composition second second)) listCons)
lemma polynomial_recordAdvance : PolynomialTime recordAdvanceRealizer := by
  unfold recordAdvanceRealizer
  have hn : PolynomialTime (composition
      (f := fun z : List Bool × RecordState => (z.1,z.2.1)) (g := advance)
      (pair first (composition second first)) advanceRealizer) :=
    polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) polynomial_advance
  exact polynomial_pair hn (polynomial_composition (polynomial_pair
    (polynomial_composition hn polynomial_second) (polynomial_composition polynomial_second polynomial_second))
    polynomial_listCons)

lemma recordFold_bounds_fixed (words : List (List Bool)) (state : RecordState) (S : ℕ)
    (hfixed : weight state.1.1 ≤ S) (hcurrent : weight state.1 ≤ 10*(S+1)) :
    let out := words.foldl (fun state bits => recordAdvance (bits,state)) state
    out.1.1=state.1.1 ∧ weight out.1 ≤ 10*(S+1) ∧
      weight out.2 ≤ weight state.2+words.length*(10*(S+1)+1) := by
  induction words generalizing state with
  | nil => exact ⟨rfl,hcurrent,by simp⟩
  | cons word words ih =>
    have hn := advance_weight word state.1 S hfixed
    have hh := ih (recordAdvance (word,state)) hfixed hn
    simp only [List.foldl_cons]
    dsimp only at hh ⊢
    refine ⟨hh.1,hh.2.1,?_⟩
    have hb : weight (advance (word,state.1)).2 ≤ 10*(S+1) := (weight_snd _).trans hn
    simp only [recordAdvance,weight_cons,List.length_cons] at hh ⊢
    simp only [Nat.add_mul,Nat.one_mul] at *
    omega

lemma recordFold_weight (words : List (List Bool)) (state : RecordState) (S : ℕ)
    (hw : words.length ≤ S) (hs : weight state ≤ S) :
    weight (words.foldl (fun state bits => recordAdvance (bits,state)) state) ≤ 30*(S+1)^2 := by
  have hc : weight state.1 ≤ S := (weight_fst state).trans hs
  have hf : weight state.1.1 ≤ S := (weight_fst state.1).trans hc
  have hh : weight state.2 ≤ S := (weight_snd state).trans hs
  have hb := recordFold_bounds_fixed words state S hf (hc.trans (by omega))
  dsimp only at hb
  rw [weight_prod]
  have hmul : words.length*(10*(S+1)+1) ≤ S*(10*(S+1)+1) :=
    Nat.mul_le_mul_right _ hw
  nlinarith [hb.2.1,hb.2.2]

def recordWalk (z : RecordState × List (List Bool)) : RecordState :=
  z.2.foldl (fun state bits => recordAdvance (bits,state)) z.1
def recordWalkRealizer : Realizer recordWalk :=
  composition (pair second first) (fold recordAdvanceRealizer)
theorem polynomial_recordWalk : PolynomialTime recordWalkRealizer := by
  apply polynomial_composition (polynomial_pair polynomial_second polynomial_first)
  apply polynomial_fold polynomial_recordAdvance (30*(X+1)^2)
  intro words state pre post he
  simp only [eval_mul,eval_ofNat,eval_add,eval_X,eval_one,eval_pow]
  apply recordFold_weight pre state (weight (words,state))
  · have hp : pre.length ≤ words.length := by rw [he,List.length_append]; omega
    exact hp.trans ((list_length_le_weight words).trans (weight_fst (words,state)))
  · exact weight_snd (words,state)

def initialRecord (state : State) : RecordState := (state,[state.2])
def initialRecordRealizer : Realizer initialRecord :=
  pair identity (composition (pair second (constant ([] : List (List ℕ)))) listCons)
lemma polynomial_initialRecord : PolynomialTime initialRecordRealizer :=
  polynomial_pair polynomial_identity (polynomial_composition
    (polynomial_pair polynomial_second (polynomial_constant [])) polynomial_listCons)

def history (z : State × List (List Bool)) : List (List ℕ) :=
  (recordWalk (initialRecord z.1,z.2)).2.reverse
def historyRealizer : Realizer history :=
  composition (f := fun z : State × List (List Bool) => (initialRecord z.1,z.2))
    (g := fun z : RecordState × List (List Bool) => (recordWalk z).2.reverse)
    (pair (composition first initialRecordRealizer) second)
    (composition (composition recordWalkRealizer second) reverse)
theorem polynomial_history : PolynomialTime historyRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_initialRecord) polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_recordWalk polynomial_second)
      polynomial_reverse)

end ContingencyTables.CompanionBoundedWalkProgram

end OAI
