import OAI.Combinatorics.ContingencyTables.Counting.CompanionMultiplierMatrixProgram
import OAI.Combinatorics.ContingencyTables.Machines.FractionAggregateProgram

namespace OAI

/-! # Executing the observed ratio and learned phase update

The supplied pairs contain the current and next weight queries for every
observed state. Only plain states contribute to the ratio. The same actual
trajectory supplies the plain/defect counts and the abort test.
-/
namespace ContingencyTables.CompanionPhaseFinishProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open CompanionTraceProgram CompanionMultiplierMatrixProgram CompanionPhaseCounts

abbrev Fraction := TreeFraction.Fraction
abbrev Stored := FractionMatrix×Fraction
abbrev Input := ((ReturnInput×FractionMatrix)×Fraction)×List (Fraction×Fraction)
abbrev TermInput := CompanionChainValidator.ValidatorInput×(Fraction×Fraction)

def term (z : TermInput) : Fraction :=
  if CompanionTraceProgram.pairedPlainTest z.1 then TreeFraction.div (z.2.2,z.2.1) else (0,1)
def termRealizer : Realizer term :=
  choose (composition (f := fun z : TermInput => z.1) (g := CompanionTraceProgram.pairedPlainTest)
      first CompanionTraceProgram.pairedPlainTestRealizer)
    (composition (f := fun z : TermInput => (z.2.2,z.2.1)) (g := TreeFraction.div)
      (pair (composition second second) (composition second first)) TreeFraction.divRealizer)
    (constant (0,1))
lemma polynomial_term : PolynomialTime termRealizer :=
  polynomial_choose (polynomial_composition polynomial_first CompanionTraceProgram.polynomial_pairedPlainTest)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
      (polynomial_composition polynomial_second polynomial_first)) TreeFraction.polynomial_div)
    (polynomial_constant (0,1))

lemma term_den_pos (z : TermInput) : 0 < (term z).2 := by
  unfold term
  split_ifs
  · exact TreeFraction.normalize_den_pos _
  · decide

def trajectory (z : Input) : ReturnInput := z.1.1.1
def trajectoryRealizer : Realizer trajectory := composition (composition first first) first
lemma polynomial_trajectory : PolynomialTime trajectoryRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first

def indices (z : Input) : List ℕ := List.range (trajectory z).2.length
def indicesRealizer : Realizer indices :=
  composition (composition (composition trajectoryRealizer second) listLength) range
lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_trajectory polynomial_second) polynomial_listLength) X
  intro z
  simpa only [eval_X,Function.comp_apply] using
    (list_length_le_weight (trajectory z).2).trans
      ((weight_snd (trajectory z)).trans
        ((weight_fst z.1.1).trans ((weight_fst z.1).trans (weight_fst z))))

def termInput (z : Input×ℕ) : TermInput :=
  (((trajectory z.1).1,(trajectory z.1).2.getD z.2 []),z.1.2.getD z.2 ((0,1),(0,1)))
def termInputRealizer : Realizer termInput :=
  pair (pair (composition (composition (f := fun z : Input×ℕ => z.1) (g := trajectory) first trajectoryRealizer) first)
    (composition (pair (composition (composition (f := fun z : Input×ℕ => z.1) (g := trajectory) first trajectoryRealizer) second) second) (getDFast [])))
    (composition (pair (composition first second) second) (getDFast ((0,1),(0,1))))
lemma polynomial_termInput : PolynomialTime termInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_trajectory) polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_trajectory) polynomial_second)
      polynomial_second) (polynomial_getDFast [])))
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
      polynomial_second) (polynomial_getDFast ((0,1),(0,1))))

def indexedTerm (z : Input×ℕ) : Fraction := term (termInput z)
def indexedTermRealizer : Realizer indexedTerm :=
  composition (f := termInput) (g := term) termInputRealizer termRealizer
lemma polynomial_indexedTerm : PolynomialTime indexedTermRealizer :=
  polynomial_composition polynomial_termInput polynomial_term

def terms (z : Input) : List Fraction := (indices z).map (fun i => indexedTerm (z,i))
def termsRealizer : Realizer terms := composition (pair identity indicesRealizer) (mapWith indexedTermRealizer)
lemma polynomial_terms : PolynomialTime termsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_indexedTerm)

attribute [local irreducible] trajectory terms

def total (z : Input) : Fraction := TreeFraction.sum (terms z)
def totalRealizer : Realizer total :=
  composition (f := terms) (g := TreeFraction.sum) termsRealizer TreeFraction.sumRealizer
lemma polynomial_total : PolynomialTime totalRealizer :=
  polynomial_composition polynomial_terms TreeFraction.polynomial_sum

def count (z : Input) : Fraction := (plainCountCode (trajectory z),1)
def countRealizer : Realizer count :=
  pair (composition (f := trajectory) (g := plainCountCode) trajectoryRealizer plainCountRealizer) (constant 1)
lemma polynomial_count : PolynomialTime countRealizer :=
  polynomial_pair (polynomial_composition polynomial_trajectory polynomial_plainCount) (polynomial_constant 1)

def ratio (z : Input) : Fraction := TreeFraction.div (total z,count z)
def ratioRealizer : Realizer ratio :=
  composition (f := fun z : Input => (total z,count z)) (g := TreeFraction.div)
    (pair totalRealizer countRealizer) TreeFraction.divRealizer
lemma polynomial_ratio : PolynomialTime ratioRealizer :=
  polynomial_composition (polynomial_pair polynomial_total polynomial_count) TreeFraction.polynomial_div

attribute [local irreducible] ratio

def estimate (z : Input) : Fraction := TreeFraction.mul (z.1.2,ratio z)
def estimateRealizer : Realizer estimate :=
  composition (f := fun z : Input => (z.1.2,ratio z)) (g := TreeFraction.mul)
    (pair (composition first second) ratioRealizer) TreeFraction.mulRealizer
lemma polynomial_estimate : PolynomialTime estimateRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    polynomial_ratio) TreeFraction.polynomial_mul

def next (z : Input) : Stored := (updateMatrix z.1.1,estimate z)
def nextRealizer : Realizer next :=
  pair (composition (f := fun z : Input => z.1.1) (g := updateMatrix)
    (composition first first) updateMatrixRealizer) estimateRealizer
lemma polynomial_next : PolynomialTime nextRealizer :=
  polynomial_pair (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    polynomial_updateMatrix) polynomial_estimate

attribute [local irreducible] next

def output (z : Input) : Option Stored :=
  if positiveCounts (trajectory z) then some (next z) else none
def outputRealizer : Realizer output :=
  choose (composition (f := trajectory) (g := positiveCounts) trajectoryRealizer positiveCountsRealizer)
    (composition (f := next) (g := Option.some) nextRealizer TreeTyped.some) (constant none)
lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_choose (polynomial_composition polynomial_trajectory polynomial_positiveCounts)
    (polynomial_composition polynomial_next polynomial_some) (polynomial_constant none)

end ContingencyTables.CompanionPhaseFinishProgram

end OAI
