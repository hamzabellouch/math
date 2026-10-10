import OAI.Combinatorics.ContingencyTables.Dense.DenseFlatExponentProgram
import OAI.Combinatorics.ContingencyTables.Machines.DyadicWordProgram

namespace OAI

/-! # A polynomial binary program for a full dense Metropolis step -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev FlatStepData := FlatExponentData×(List Bool×List Bool)

def replaceFlat (z : FlatExponentData×List ℕ) : FlatExponentData :=
  ((z.1.1.1,z.2),z.1.2)

def replaceFlatRealizer : Realizer replaceFlat :=
  pair (pair (composition (composition first first) first) second) (composition first second)

lemma polynomial_replaceFlat : PolynomialTime replaceFlatRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_second) (polynomial_composition polynomial_first polynomial_second)

def flatAcceptCandidate (z : FlatStepData×List ℕ) : List ℕ :=
  if dyadicWordAccept (z.1.2.2,
    flatExponent (replaceFlat (z.1.1,z.2))-flatExponent z.1.1) then z.2 else z.1.1.1.2

def flatAcceptCandidateRealizer : Realizer flatAcceptCandidate := by
  let data : Realizer (fun z : FlatStepData×List ℕ => z.1.1) := composition first first
  let candidate := composition (composition (pair data second) replaceFlatRealizer) flatExponentRealizer
  let current := composition data flatExponentRealizer
  let gap := composition (pair candidate current) subtract
  let coins : Realizer (fun z : FlatStepData×List ℕ => z.1.2.2) :=
    composition (composition first second) second
  exact choose (composition (pair coins gap) dyadicWordAcceptRealizer) second
    (composition (composition data first) second)

theorem polynomial_flatAcceptCandidate : PolynomialTime flatAcceptCandidateRealizer := by
  have hd : PolynomialTime (composition
      (first (A := FlatStepData) (B := List ℕ)) first) :=
    polynomial_composition polynomial_first polynomial_first
  have hc := polynomial_composition (polynomial_composition
    (polynomial_pair hd polynomial_second) polynomial_replaceFlat) polynomial_flatExponent
  have hx := polynomial_composition hd polynomial_flatExponent
  have hg := polynomial_composition (polynomial_pair hc hx) polynomial_subtract
  have hb : PolynomialTime (composition
      (composition (first (A := FlatStepData) (B := List ℕ)) second) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second
  unfold flatAcceptCandidateRealizer
  exact polynomial_choose (polynomial_composition (polynomial_pair hb hg) polynomial_dyadicWordAccept)
    polynomial_second (polynomial_composition (polynomial_composition hd polynomial_first) polynomial_second)

def flatStepCandidate (z : FlatStepData) : Option (List ℕ) :=
  axisWordStep ((4*z.1.2^8,z.1.1.2),z.2.1)

def flatStepCandidateRealizer : Realizer flatStepCandidate := by
  let d : Realizer (fun z : FlatStepData => z.1.2) := composition first second
  let K := composition (pair (constant 4) (composition d eighthPower)) multiply
  let xs : Realizer (fun z : FlatStepData => z.1.1.2) :=
    composition (composition first first) second
  exact composition (pair (pair K xs) (composition second first)) axisWordStepRealizer

theorem polynomial_flatStepCandidate : PolynomialTime flatStepCandidateRealizer := by
  have hd : PolynomialTime (composition
      (first (A := FlatExponentData) (B := List Bool×List Bool)) second) :=
    polynomial_composition polynomial_first polynomial_second
  have hK := polynomial_composition (polynomial_pair (polynomial_constant 4)
    (polynomial_composition hd polynomial_eighthPower)) polynomial_multiply
  unfold flatStepCandidateRealizer
  exact polynomial_composition (polynomial_pair (polynomial_pair hK
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second))
    (polynomial_composition polynomial_second polynomial_first)) polynomial_axisWordStep

def flatMetropolisStep (z : FlatStepData) : List ℕ :=
  (flatStepCandidate z).elim z.1.1.2 (fun xs => flatAcceptCandidate (z,xs))

def flatMetropolisStepRealizer : Realizer flatMetropolisStep :=
  composition (pair identity flatStepCandidateRealizer)
    (optionCases (composition (composition first first) second) flatAcceptCandidateRealizer)

/-- Includes proposal decoding, exact integer exponent evaluation and the
independent acceptance word. Every finite input terminates in polynomial time. -/
theorem polynomial_flatMetropolisStep : PolynomialTime flatMetropolisStepRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_flatStepCandidate)
    (polynomial_optionCases
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_flatAcceptCandidate)

end ContingencyTables.DensePrograms

end OAI
