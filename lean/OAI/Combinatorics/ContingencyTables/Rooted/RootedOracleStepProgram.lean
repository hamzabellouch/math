import OAI.Combinatorics.ContingencyTables.Rooted.RootedCatalogStep
import OAI.Combinatorics.ContingencyTables.Dense.DenseMetropolisSemantics

namespace OAI

/-! # Polynomial execution of the catalog-order oracle step

The program uses the computed forest exponent twice, one arithmetic
axis proposal and one independent bounded dyadic acceptance word.
-/

namespace ContingencyTables.RootedOracleStepProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

abbrev Data := ℕ×RootedPenaltyEvaluateProgram.Input
abbrev StepInput := Data×(List Bool×List Bool)

def replace (z : RootedPenaltyEvaluateProgram.Input×List ℕ) :
    RootedPenaltyEvaluateProgram.Input := (z.1.1,(z.1.2.1,z.2))
def replaceRealizer : Realizer replace :=
  pair (composition first first) (pair (composition (composition first second) first) second)
lemma polynomial_replace : PolynomialTime replaceRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_first) polynomial_second)

def candidate (z : StepInput) : Option (List ℕ) :=
  axisWordStep ((z.1.1,z.1.2.2.2),z.2.1)
def candidateRealizer : Realizer candidate :=
  composition (f := fun z : StepInput => ((z.1.1,z.1.2.2.2),z.2.1)) (g := axisWordStep)
    (pair (pair (composition first first)
      (composition (composition (composition first second) second) second))
      (composition second first)) axisWordStepRealizer
lemma polynomial_candidate : PolynomialTime candidateRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_second) polynomial_second))
    (polynomial_composition polynomial_second polynomial_first)) polynomial_axisWordStep

def currentData (z : StepInput×List ℕ) : RootedPenaltyEvaluateProgram.Input := z.1.1.2
def currentDataRealizer : Realizer currentData := composition (composition first first) second
lemma polynomial_currentData : PolynomialTime currentDataRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second

def candidateData (z : StepInput×List ℕ) : RootedPenaltyEvaluateProgram.Input :=
  replace (currentData z,z.2)
def candidateDataRealizer : Realizer candidateData :=
  composition (f := fun z : StepInput×List ℕ => (currentData z,z.2)) (g := replace)
    (pair currentDataRealizer second) replaceRealizer
lemma polynomial_candidateData : PolynomialTime candidateDataRealizer :=
  polynomial_composition (polynomial_pair polynomial_currentData polynomial_second) polynomial_replace

def gap (z : StepInput×List ℕ) : ℕ :=
  RootedPenaltyEvaluateProgram.evaluate (candidateData z)-
    RootedPenaltyEvaluateProgram.evaluate (currentData z)
def gapRealizer : Realizer gap :=
  composition (f := fun z : StepInput×List ℕ =>
    (RootedPenaltyEvaluateProgram.evaluate (candidateData z),
      RootedPenaltyEvaluateProgram.evaluate (currentData z))) (g := fun z => z.1-z.2)
    (pair
      (composition (f := candidateData) (g := RootedPenaltyEvaluateProgram.evaluate)
        candidateDataRealizer RootedPenaltyEvaluateProgram.evaluateRealizer)
      (composition (f := currentData) (g := RootedPenaltyEvaluateProgram.evaluate)
        currentDataRealizer RootedPenaltyEvaluateProgram.evaluateRealizer)) subtract
lemma polynomial_gap : PolynomialTime gapRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_candidateData RootedPenaltyEvaluateProgram.polynomial_evaluate)
    (polynomial_composition polynomial_currentData RootedPenaltyEvaluateProgram.polynomial_evaluate))
    polynomial_subtract

def acceptCandidate (z : StepInput×List ℕ) : List ℕ :=
  if dyadicWordAccept (z.1.2.2,gap z) then z.2 else z.1.1.2.2.2
def acceptCandidateRealizer : Realizer acceptCandidate :=
  choose
    (composition (f := fun z : StepInput×List ℕ => (z.1.2.2,gap z)) (g := dyadicWordAccept)
      (pair (composition (composition first second) second) gapRealizer) dyadicWordAcceptRealizer)
    second (composition (composition currentDataRealizer second) second)
lemma polynomial_acceptCandidate : PolynomialTime acceptCandidateRealizer :=
  polynomial_choose (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second)
    polynomial_gap) polynomial_dyadicWordAccept) polynomial_second
    (polynomial_composition (polynomial_composition polynomial_currentData polynomial_second)
      polynomial_second)

def step (z : StepInput) : List ℕ :=
  (candidate z).elim z.1.2.2.2 (fun xs => acceptCandidate (z,xs))
def stepRealizer : Realizer step :=
  composition (f := fun z : StepInput => (z,candidate z))
    (g := fun z => z.2.elim z.1.1.2.2.2 (fun xs => acceptCandidate (z.1,xs)))
    (pair identity candidateRealizer)
    (optionCases (composition (composition (composition first second) second) second)
      acceptCandidateRealizer)
theorem polynomial_step : PolynomialTime stepRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_candidate)
    (polynomial_optionCases
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_second) polynomial_second) polynomial_second)
      polynomial_acceptCandidate)

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FairBits

noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) : Data :=
  (K,(((A.d,A.W),(C,a)),
    (RootedDemandProgram.data A (ForestCountIdentification.smallX A.small z)
      (fun i j => A.b i j-ForestCountIdentification.smallY A.small z i j),gridNatCode v)))

lemma evaluate_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    RootedPenaltyEvaluateProgram.evaluate (data A C a K z v).2=
      RootedCatalogGrid.exponent A C a z v :=
  RootedCatalogGrid.evaluate_grid A C a K hC z v

lemma replace_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (z : View A → ℕ) (v w : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    replace ((data A C a K z v).2,gridNatCode w)=(data A C a K z w).2 := rfl

theorem step_pair (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    {p k : ℕ} (proposal : Fin p → Bool) (coins : Fin k → Bool) :
    step (data A C a K z v,(List.ofFn proposal,List.ofFn coins))=
      gridNatCode (match axisCodeStep v (binaryWordEquiv p proposal) with
        | Option.none => v
        | Option.some w => if acceptDyadic
            (RootedCatalogGrid.exponent A C a z w-RootedCatalogGrid.exponent A C a z v)
            k (binaryWordEquiv k coins) then w else v) := by
  have hc : candidate (data A C a K z v,(List.ofFn proposal,List.ofFn coins))=
      (axisCodeStep v (binaryWordEquiv p proposal)).map gridNatCode :=
    axisWordStep_eq v proposal
  unfold step
  rw [hc]
  cases h : axisCodeStep v (binaryWordEquiv p proposal) with
  | none => rfl
  | some w =>
    simp only [Option.map_some,Option.elim_some,acceptCandidate,gap,candidateData,currentData,
      replace_data,evaluate_data A C a K hC,dyadicWordAccept_ofFn,decide_eq_true_eq]
    split_ifs <;> rfl

end
end ContingencyTables.RootedOracleStepProgram

end OAI
