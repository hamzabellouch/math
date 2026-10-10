import OAI.Combinatorics.ContingencyTables.Machines.ScheduledResidualProgram
import OAI.Combinatorics.ContingencyTables.Sampling.CompiledResidualCorrection

namespace OAI

/-! # Computing the exact sampler's precision from its margin-only input -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] marginDimension marginBinaryLength parameterWordCount

def sixthPower : Realizer (fun n : ℕ => n^6) :=
  (composition (f := fun n : ℕ => n^3) (g := fun n : ℕ => n^2)
    cubicPower squarePower).congr (by intro n; simp only [Function.comp_apply,←pow_mul])

lemma polynomial_sixthPower : PolynomialTime sixthPower :=
  polynomial_congr _ (polynomial_composition polynomial_cubicPower polynomial_squarePower)

def exactPrecision (z : CompletionMargins) : ℕ := (marginDimension z)^6*(marginBinaryLength z)^2

def exactPrecisionRealizer : Realizer exactPrecision :=
  composition (f := fun z : CompletionMargins => ((marginDimension z)^6,(marginBinaryLength z)^2))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (f := marginDimension) (g := fun n : ℕ => n^6) marginDimensionRealizer sixthPower)
      (composition (f := marginBinaryLength) (g := fun n : ℕ => n^2) marginBinaryLengthRealizer squarePower))
    multiply

lemma polynomial_exactPrecision : PolynomialTime exactPrecisionRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_marginDimension polynomial_sixthPower)
    (polynomial_composition polynomial_marginBinaryLength polynomial_squarePower)) polynomial_multiply

attribute [local irreducible] exactPrecision

def exactSamplingParameters (z : CompletionMargins) : SamplingParameters := (z,2*exactPrecision z)

def exactSamplingParametersRealizer : Realizer exactSamplingParameters :=
  pair identity (composition (f := fun z : CompletionMargins => (2,exactPrecision z))
    (g := fun p : ℕ×ℕ => p.1*p.2) (pair (constant 2) exactPrecisionRealizer) multiply)

lemma polynomial_exactSamplingParameters : PolynomialTime exactSamplingParametersRealizer :=
  polynomial_pair polynomial_identity (polynomial_composition
    (polynomial_pair (polynomial_constant 2) polynomial_exactPrecision) polynomial_multiply)

def exactBranchDenominator (z : CompletionMargins) : ℕ := BinaryPowerPrograms.power (2,exactPrecision z)

def exactBranchDenominatorRealizer : Realizer exactBranchDenominator :=
  composition (f := fun z : CompletionMargins => (2,exactPrecision z)) (g := BinaryPowerPrograms.power)
    (pair (constant 2) exactPrecisionRealizer) BinaryPowerPrograms.powerRealizer

def exactParameterMeasure (z : CompletionMargins) : ℕ := exactPrecision z+weight z

lemma work_exactBranchDenominator : WorkBound exactBranchDenominatorRealizer exactParameterMeasure := by
  unfold exactBranchDenominatorRealizer
  apply work_composition (work_of_polynomial (polynomial_pair (polynomial_constant 2)
    polynomial_exactPrecision) X (by intro z; simp only [eval_X,exactParameterMeasure]; omega))
    BinaryPowerPrograms.work_power (X+C (weight (2:ℕ)))
  intro z
  simp only [eval_add,eval_X,eval_C,exactParameterMeasure]
  omega

def exactResidualInput (z : CompletionMargins) : SamplingParameters×ℕ :=
  (exactSamplingParameters z,exactBranchDenominator z)

def exactResidualInputRealizer : Realizer exactResidualInput :=
  pair exactSamplingParametersRealizer exactBranchDenominatorRealizer

lemma work_exactResidualInput : WorkBound exactResidualInputRealizer exactParameterMeasure :=
  work_pair (work_of_polynomial polynomial_exactSamplingParameters X
    (by intro z; simp only [eval_X,exactParameterMeasure]; omega))
    work_exactBranchDenominator X (by intro z; simp only [eval_X,exactParameterMeasure]; omega)

/-- The ordinary branch needs precisely the existing public sampler's word. -/
def exactOrdinaryBits (z : CompletionMargins) : ℕ := parameterWordCount (exactSamplingParameters z)

def exactOrdinaryBitsRealizer : Realizer exactOrdinaryBits :=
  composition (f := exactSamplingParameters) (g := parameterWordCount)
    exactSamplingParametersRealizer parameterWordCountRealizer

lemma polynomial_exactOrdinaryBits : PolynomialTime exactOrdinaryBitsRealizer :=
  polynomial_composition polynomial_exactSamplingParameters polynomial_parameterWordCount

def exactParsedMargins (as : List Symbol) : CompletionMargins := (parsedSampling as).1

def exactParsedMarginsRealizer : Realizer exactParsedMargins :=
  composition (f := parsedSampling) (g := fun p : SamplingParameters => p.1) parsedSamplingRealizer first

lemma polynomial_exactParsedMargins : PolynomialTime exactParsedMarginsRealizer :=
  polynomial_composition polynomial_parsedSampling polynomial_first

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms MatchingFPRAS.LiteralParse
open scoped BigOperators

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma exactPrecision_ofFn : exactPrecision (List.ofFn r,List.ofFn c)=correctionPrecision r c := by
  rw [exactPrecision,marginDimension_ofFn,marginBinaryLength_ofFn]
  rfl

lemma exactSamplingParameters_ofFn :
    exactSamplingParameters (List.ofFn r,List.ofFn c)=
      ((List.ofFn r,List.ofFn c),2*correctionPrecision r c) := by
  rw [exactSamplingParameters,exactPrecision_ofFn]

lemma exactBranchDenominator_ofFn :
    exactBranchDenominator (List.ofFn r,List.ofFn c)=2^(correctionPrecision r c) := by
  rw [exactBranchDenominator,BinaryPowerPrograms.power_eq,exactPrecision_ofFn]

lemma exactResidualInput_ofFn :
    exactResidualInput (List.ofFn r,List.ofFn c)=
      (((List.ofFn r,List.ofFn c),2*correctionPrecision r c),2^(correctionPrecision r c)) := by
  rw [exactResidualInput,exactSamplingParameters_ofFn,exactBranchDenominator_ofFn]

lemma exactOrdinaryBits_ofFn :
    exactOrdinaryBits (List.ofFn r,List.ofFn c)=finiteSamplerBits r c (2*correctionPrecision r c) := by
  rw [exactOrdinaryBits,exactSamplingParameters_ofFn,parameterWordCount_ofFn]

lemma exactParsedMargins_spec :
    exactParsedMargins (Algorithms.encodeMargins r c)=(List.ofFn r,List.ofFn c) := by
  unfold exactParsedMargins parsedSampling samplingInput
  rw [GreedyFeasibleTable.encodeMargins_natWords,GreedyFeasibleTable.parse_natWords]
  have h := GreedyFeasibleTable.marginLists_spec m n (List.ofFn r) (List.ofFn c) []
    List.length_ofFn List.length_ofFn
  simpa only [List.append_nil] using h

end ContingencyTables.SmallGraphProfiles

end OAI
