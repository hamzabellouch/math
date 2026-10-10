import OAI.Combinatorics.ContingencyTables.Counting.CompanionFlatReturnProgram

namespace OAI

/-! # Bounded iteration of the executed capped-return routine

The numeric repetition count only truncates chunks of the supplied
word. The stored profile is clipped to the fixed initial dimension,
which is redundant on every actual encoded state.
-/

namespace ContingencyTables.CompanionRepeatedReturnProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial DensePrograms

abbrev Fixed := CompanionBoundedWalkProgram.Fixed × ℕ
abbrev State := Fixed × List ℕ
abbrev Input := (State × ℕ) × List Bool

def returnInput (z : List Bool × State) : CompanionFlatReturnProgram.Input :=
  ((((z.2.1.1.1,z.2.2),z.2.2),z.2.1.2+1),z.1)
def returnInputRealizer : Realizer returnInput := by
  let frame : Realizer (fun z : List Bool × State => z.2.1.1.1) :=
    composition (composition (composition second first) first) first
  let current : Realizer (fun z : List Bool × State => z.2.2) := composition second second
  let cap : Realizer (fun z : List Bool × State => z.2.1.2+1) :=
    composition (f := fun z : List Bool × State => z.2.1.2) (g := Nat.succ)
      (composition (composition second first) second) successor
  exact pair (pair (pair (pair frame current) current) cap) first
lemma polynomial_returnInput : PolynomialTime returnInputRealizer := by
  unfold returnInputRealizer
  exact polynomial_pair (polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition
      polynomial_second polynomial_first) polynomial_first) polynomial_first)
    (polynomial_composition polynomial_second polynomial_second))
    (polynomial_composition polynomial_second polynomial_second))
    (polynomial_composition (polynomial_composition (polynomial_composition
      polynomial_second polynomial_first) polynomial_second) polynomial_successor)) polynomial_first

def candidate (z : List Bool × State) : List ℕ := CompanionFlatReturnProgram.output (returnInput z)
def candidateRealizer : Realizer candidate :=
  composition (f := returnInput) (g := CompanionFlatReturnProgram.output)
    returnInputRealizer CompanionFlatReturnProgram.outputRealizer
lemma polynomial_candidate : PolynomialTime candidateRealizer :=
  polynomial_composition polynomial_returnInput CompanionFlatReturnProgram.polynomial_output

def bound (z : List Bool × State) : ℕ := z.2.1.1.2.length
def boundRealizer : Realizer bound :=
  composition (composition (composition (composition second first) first) second) listLength
lemma polynomial_bound : PolynomialTime boundRealizer := by
  unfold boundRealizer
  exact polynomial_composition (polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_second polynomial_first) polynomial_first)
    polynomial_second) polynomial_listLength

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

lemma advance_weight (word : List Bool) (state : State) (S : ℕ) (hs : weight state.1 ≤ S) :
    weight (advance (word,state)) ≤ 10*(S+1) := by
  have hb : state.1.1.2.length ≤ S := (list_length_le_weight _).trans
    ((weight_snd state.1.1).trans ((weight_fst state.1).trans hs))
  have hn := ProfilePrograms.capView_weight state.1.1.2.length 1 (candidate (word,state))
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

def widthInput (fixed : Fixed) : CompanionMetropolisWordProgram.Input :=
  ((fixed.1.1,fixed.1.2),[])
def widthInputRealizer : Realizer widthInput :=
  pair (pair (composition first first) (composition first second)) (constant [])
lemma polynomial_widthInput : PolynomialTime widthInputRealizer := by
  unfold widthInputRealizer
  exact polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition polynomial_first polynomial_second)) (polynomial_constant [])

def blockWidth (fixed : Fixed) : ℕ :=
  (fixed.2+1)*CompanionTransitionWidth.width (widthInput fixed)
def blockWidthRealizer : Realizer blockWidth :=
  composition (f := fun fixed : Fixed => (fixed.2+1,CompanionTransitionWidth.width (widthInput fixed)))
    (g := fun z : ℕ × ℕ => z.1*z.2)
    (pair (composition second successor)
      (composition (f := widthInput) (g := CompanionTransitionWidth.width)
        widthInputRealizer CompanionTransitionWidth.widthRealizer)) multiply
lemma polynomial_blockWidth : PolynomialTime blockWidthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_successor)
    (polynomial_composition polynomial_widthInput CompanionTransitionWidth.polynomial_width)) polynomial_multiply

def words (z : Input) : List (List Bool) :=
  (wordChunks (blockWidth z.1.1.1,z.2)).take z.1.2
def wordsRealizer : Realizer words :=
  composition (f := fun z : Input => (wordChunks (blockWidth z.1.1.1,z.2),z.1.2))
    (g := fun z : List (List Bool) × ℕ => z.1.take z.2)
    (pair (composition (f := fun z : Input => (blockWidth z.1.1.1,z.2)) (g := wordChunks)
      (pair (composition (f := fun z : Input => z.1.1.1) (g := blockWidth)
        (composition (composition first first) first) blockWidthRealizer) second) wordChunksRealizer)
      (composition first second)) takeFast
lemma polynomial_words : PolynomialTime wordsRealizer := by
  apply polynomial_composition _ polynomial_takeFast
  apply polynomial_pair _ (polynomial_composition polynomial_first polynomial_second)
  apply polynomial_composition _ polynomial_wordChunks
  apply polynomial_pair _ polynomial_second
  exact polynomial_composition (by tree_poly) polynomial_blockWidth

def output (z : Input) : List ℕ := (walk (z.1.1,words z)).2
def outputRealizer : Realizer output :=
  composition (f := fun z : Input => (z.1.1,words z)) (g := fun z => (walk z).2)
    (pair (composition first first) wordsRealizer)
    (composition (f := walk) (g := Prod.snd) walkRealizer second)
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    polynomial_words) (polynomial_composition polynomial_walk polynomial_second)

end ContingencyTables.CompanionRepeatedReturnProgram

end OAI
