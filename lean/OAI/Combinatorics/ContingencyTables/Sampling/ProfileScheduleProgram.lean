import OAI.Combinatorics.ContingencyTables.Sampling.OriginalProfileProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileRetryProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseTrialProgram
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperBinaryParameters

namespace OAI

/-! # Computing the complete outer sampling schedule from binary margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

abbrev SamplingParameters := (List ℕ×List ℕ)×ℕ

def squarePower : Realizer (fun n : ℕ => n^2) :=
  squareNat.congr (fun n => (pow_two n).symm)

theorem polynomial_squarePower : PolynomialTime squarePower :=
  polynomial_congr _ polynomial_squareNat

def cubicPower : Realizer (fun n : ℕ => n^3) :=
  (composition (pair squareNat identity) multiply).congr (by
    intro n; simp only [Function.comp_apply,id_eq]; ring)

theorem polynomial_cubicPower : PolynomialTime cubicPower :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair polynomial_squareNat polynomial_identity) polynomial_multiply)

def twelfthPower : Realizer (fun n : ℕ => n^12) :=
  (composition fourthPower cubicPower).congr (by
    intro n; simp only [Function.comp_apply,←pow_mul])

theorem polynomial_twelfthPower : PolynomialTime twelfthPower :=
  polynomial_congr _ (polynomial_composition polynomial_fourthPower polynomial_cubicPower)

def twoHundredthPower : Realizer (fun n : ℕ => n^200) :=
  (composition fiftiethPower fourthPower).congr (by
    intro n; simp only [Function.comp_apply,←pow_mul])

theorem polynomial_twoHundredthPower : PolynomialTime twoHundredthPower :=
  polynomial_congr _ (polynomial_composition polynomial_fiftiethPower polynomial_fourthPower)

def sixtySecondPower : Realizer (fun n : ℕ => n^62) :=
  (composition (pair (composition twentiethPower cubicPower) squareNat) multiply).congr (by
    intro n; simp only [Function.comp_apply]; ring)

theorem polynomial_sixtySecondPower : PolynomialTime sixtySecondPower :=
  polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_twentiethPower polynomial_cubicPower)
    polynomial_squareNat) polynomial_multiply)

def marginPadding (z : List ℕ×List ℕ) : ℕ := (marginDimension z)^12

def marginPaddingRealizer : Realizer marginPadding :=
  composition (f := fun z : List ℕ×List ℕ => marginDimension z) (g := fun n : ℕ => n^12) (marginDimensionRealizer) twelfthPower

theorem polynomial_marginPadding : PolynomialTime marginPaddingRealizer :=
  polynomial_composition (f := fun z : List ℕ×List ℕ => marginDimension z) (g := fun n : ℕ => n^12) (polynomial_marginDimension) polynomial_twelfthPower

def marginStateBound (z : List ℕ×List ℕ) : ℕ := (((z.1.sum+(marginDimension z*marginPadding z))+marginThreshold z)+2)

def marginStateBoundRealizer : Realizer marginStateBound :=
  composition (f := fun z : List ℕ×List ℕ => (((z.1.sum+(marginDimension z*marginPadding z))+marginThreshold z),2)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (composition (f := fun z : List ℕ×List ℕ => ((z.1.sum+(marginDimension z*marginPadding z)),marginThreshold z)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (composition (f := fun z : List ℕ×List ℕ => (z.1.sum,(marginDimension z*marginPadding z))) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (composition (f := fun z : List ℕ×List ℕ => z.1) (g := List.sum) first listSum) (composition (f := fun z : List ℕ×List ℕ => (marginDimension z,marginPadding z)) (g := fun t : ℕ×ℕ => t.1*t.2) (pair (marginDimensionRealizer) (marginPaddingRealizer)) multiply)) add) (marginThresholdRealizer)) add) (constant 2)) add

theorem polynomial_marginStateBound : PolynomialTime marginStateBoundRealizer :=
  polynomial_composition (f := fun z : List ℕ×List ℕ => (((z.1.sum+(marginDimension z*marginPadding z))+marginThreshold z),2)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_composition (f := fun z : List ℕ×List ℕ => ((z.1.sum+(marginDimension z*marginPadding z)),marginThreshold z)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_composition (f := fun z : List ℕ×List ℕ => (z.1.sum,(marginDimension z*marginPadding z))) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_composition (f := fun z : List ℕ×List ℕ => z.1) (g := List.sum) polynomial_first polynomial_listSum) (polynomial_composition (f := fun z : List ℕ×List ℕ => (marginDimension z,marginPadding z)) (g := fun t : ℕ×ℕ => t.1*t.2) (polynomial_pair (polynomial_marginDimension) (polynomial_marginPadding)) polynomial_multiply)) polynomial_add) (polynomial_marginThreshold)) polynomial_add) (polynomial_constant 2)) polynomial_add

def marginBinaryLength (z : List ℕ×List ℕ) : ℕ := (marginDimension z+(Nat.clog 2) ((marginStateBound z+2)))

def marginBinaryLengthRealizer : Realizer marginBinaryLength :=
  composition (f := fun z : List ℕ×List ℕ => (marginDimension z,(Nat.clog 2) ((marginStateBound z+2)))) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (marginDimensionRealizer) (composition (f := fun z : List ℕ×List ℕ => (marginStateBound z+2)) (g := Nat.clog 2) (composition (f := fun z : List ℕ×List ℕ => (marginStateBound z,2)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (marginStateBoundRealizer) (constant 2)) add) ceilLogTwoRealizer)) add

theorem polynomial_marginBinaryLength : PolynomialTime marginBinaryLengthRealizer :=
  polynomial_composition (f := fun z : List ℕ×List ℕ => (marginDimension z,(Nat.clog 2) ((marginStateBound z+2)))) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_marginDimension) (polynomial_composition (f := fun z : List ℕ×List ℕ => (marginStateBound z+2)) (g := Nat.clog 2) (polynomial_composition (f := fun z : List ℕ×List ℕ => (marginStateBound z,2)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_marginStateBound) (polynomial_constant 2)) polynomial_add) polynomial_ceilLogTwo)) polynomial_add

def parameterDimension (z : SamplingParameters) : ℕ := marginDimension z.1

def parameterDimensionRealizer : Realizer parameterDimension :=
  composition (f := fun z : SamplingParameters => z.1) (g := marginDimension) first marginDimensionRealizer

theorem polynomial_parameterDimension : PolynomialTime parameterDimensionRealizer :=
  polynomial_composition (f := fun z : SamplingParameters => z.1) (g := marginDimension) polynomial_first polynomial_marginDimension

def parameterBinaryLength (z : SamplingParameters) : ℕ := marginBinaryLength z.1

def parameterBinaryLengthRealizer : Realizer parameterBinaryLength :=
  composition (f := fun z : SamplingParameters => z.1) (g := marginBinaryLength) first marginBinaryLengthRealizer

theorem polynomial_parameterBinaryLength : PolynomialTime parameterBinaryLengthRealizer :=
  polynomial_composition (f := fun z : SamplingParameters => z.1) (g := marginBinaryLength) polynomial_first polynomial_marginBinaryLength

def parameterTrials (z : SamplingParameters) : ℕ := ((parameterDimension z)^4*(z.2+1))

def parameterTrialsRealizer : Realizer parameterTrials :=
  composition (f := fun z : SamplingParameters => ((parameterDimension z)^4,(z.2+1))) (g := fun t : ℕ×ℕ => t.1*t.2) (pair (composition (f := fun z : SamplingParameters => parameterDimension z) (g := fun n : ℕ => n^4) (parameterDimensionRealizer) fourthPower) (composition (f := fun z : SamplingParameters => (z.2,1)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (second) (constant 1)) add)) multiply

theorem polynomial_parameterTrials : PolynomialTime parameterTrialsRealizer :=
  polynomial_composition (f := fun z : SamplingParameters => ((parameterDimension z)^4,(z.2+1))) (g := fun t : ℕ×ℕ => t.1*t.2) (polynomial_pair (polynomial_composition (f := fun z : SamplingParameters => parameterDimension z) (g := fun n : ℕ => n^4) (polynomial_parameterDimension) polynomial_fourthPower) (polynomial_composition (f := fun z : SamplingParameters => (z.2,1)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_second) (polynomial_constant 1)) polynomial_add)) polynomial_multiply

def parameterSteps (z : SamplingParameters) : ℕ := ((parameterDimension z)^200*((z.2+parameterBinaryLength z))^2)

def parameterStepsRealizer : Realizer parameterSteps :=
  composition (f := fun z : SamplingParameters => ((parameterDimension z)^200,((z.2+parameterBinaryLength z))^2)) (g := fun t : ℕ×ℕ => t.1*t.2) (pair (composition (f := fun z : SamplingParameters => parameterDimension z) (g := fun n : ℕ => n^200) (parameterDimensionRealizer) twoHundredthPower) (composition (f := fun z : SamplingParameters => (z.2+parameterBinaryLength z)) (g := fun n : ℕ => n^2) (composition (f := fun z : SamplingParameters => (z.2,parameterBinaryLength z)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (second) (parameterBinaryLengthRealizer)) add) squarePower)) multiply

theorem polynomial_parameterSteps : PolynomialTime parameterStepsRealizer :=
  polynomial_composition (f := fun z : SamplingParameters => ((parameterDimension z)^200,((z.2+parameterBinaryLength z))^2)) (g := fun t : ℕ×ℕ => t.1*t.2) (polynomial_pair (polynomial_composition (f := fun z : SamplingParameters => parameterDimension z) (g := fun n : ℕ => n^200) (polynomial_parameterDimension) polynomial_twoHundredthPower) (polynomial_composition (f := fun z : SamplingParameters => (z.2+parameterBinaryLength z)) (g := fun n : ℕ => n^2) (polynomial_composition (f := fun z : SamplingParameters => (z.2,parameterBinaryLength z)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_second) (polynomial_parameterBinaryLength)) polynomial_add) polynomial_squarePower)) polynomial_multiply

def parameterAccuracy (z : SamplingParameters) : ℕ := ((parameterDimension z)^4*((z.2+parameterBinaryLength z))^2)

def parameterAccuracyRealizer : Realizer parameterAccuracy :=
  composition (f := fun z : SamplingParameters => ((parameterDimension z)^4,((z.2+parameterBinaryLength z))^2)) (g := fun t : ℕ×ℕ => t.1*t.2) (pair (composition (f := fun z : SamplingParameters => parameterDimension z) (g := fun n : ℕ => n^4) (parameterDimensionRealizer) fourthPower) (composition (f := fun z : SamplingParameters => (z.2+parameterBinaryLength z)) (g := fun n : ℕ => n^2) (composition (f := fun z : SamplingParameters => (z.2,parameterBinaryLength z)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (second) (parameterBinaryLengthRealizer)) add) squarePower)) multiply

theorem polynomial_parameterAccuracy : PolynomialTime parameterAccuracyRealizer :=
  polynomial_composition (f := fun z : SamplingParameters => ((parameterDimension z)^4,((z.2+parameterBinaryLength z))^2)) (g := fun t : ℕ×ℕ => t.1*t.2) (polynomial_pair (polynomial_composition (f := fun z : SamplingParameters => parameterDimension z) (g := fun n : ℕ => n^4) (polynomial_parameterDimension) polynomial_fourthPower) (polynomial_composition (f := fun z : SamplingParameters => (z.2+parameterBinaryLength z)) (g := fun n : ℕ => n^2) (polynomial_composition (f := fun z : SamplingParameters => (z.2,parameterBinaryLength z)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_second) (polynomial_parameterBinaryLength)) polynomial_add) polynomial_squarePower)) polynomial_multiply

def parameterProposalWidth (z : SamplingParameters) : ℕ := (Nat.clog 2) ((32*(parameterDimension z)^2))

def parameterProposalWidthRealizer : Realizer parameterProposalWidth :=
  composition (f := fun z : SamplingParameters => (32*(parameterDimension z)^2)) (g := Nat.clog 2) (composition (f := fun z : SamplingParameters => (32,(parameterDimension z)^2)) (g := fun t : ℕ×ℕ => t.1*t.2) (pair (constant 32) (composition (f := fun z : SamplingParameters => parameterDimension z) (g := fun n : ℕ => n^2) (parameterDimensionRealizer) squarePower)) multiply) ceilLogTwoRealizer

theorem polynomial_parameterProposalWidth : PolynomialTime parameterProposalWidthRealizer :=
  polynomial_composition (f := fun z : SamplingParameters => (32*(parameterDimension z)^2)) (g := Nat.clog 2) (polynomial_composition (f := fun z : SamplingParameters => (32,(parameterDimension z)^2)) (g := fun t : ℕ×ℕ => t.1*t.2) (polynomial_pair (polynomial_constant 32) (polynomial_composition (f := fun z : SamplingParameters => parameterDimension z) (g := fun n : ℕ => n^2) (polynomial_parameterDimension) polynomial_squarePower)) polynomial_multiply) polynomial_ceilLogTwo

def parameterCompletionWidth (z : SamplingParameters) : ℕ := (25*((((parameterDimension z+parameterBinaryLength z)+parameterAccuracy z)+1))^62)

def parameterCompletionWidthRealizer : Realizer parameterCompletionWidth :=
  composition (f := fun z : SamplingParameters => (25,((((parameterDimension z+parameterBinaryLength z)+parameterAccuracy z)+1))^62)) (g := fun t : ℕ×ℕ => t.1*t.2) (pair (constant 25) (composition (f := fun z : SamplingParameters => (((parameterDimension z+parameterBinaryLength z)+parameterAccuracy z)+1)) (g := fun n : ℕ => n^62) (composition (f := fun z : SamplingParameters => (((parameterDimension z+parameterBinaryLength z)+parameterAccuracy z),1)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (composition (f := fun z : SamplingParameters => ((parameterDimension z+parameterBinaryLength z),parameterAccuracy z)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (composition (f := fun z : SamplingParameters => (parameterDimension z,parameterBinaryLength z)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (parameterDimensionRealizer) (parameterBinaryLengthRealizer)) add) (parameterAccuracyRealizer)) add) (constant 1)) add) sixtySecondPower)) multiply

theorem polynomial_parameterCompletionWidth : PolynomialTime parameterCompletionWidthRealizer :=
  polynomial_composition (f := fun z : SamplingParameters => (25,((((parameterDimension z+parameterBinaryLength z)+parameterAccuracy z)+1))^62)) (g := fun t : ℕ×ℕ => t.1*t.2) (polynomial_pair (polynomial_constant 25) (polynomial_composition (f := fun z : SamplingParameters => (((parameterDimension z+parameterBinaryLength z)+parameterAccuracy z)+1)) (g := fun n : ℕ => n^62) (polynomial_composition (f := fun z : SamplingParameters => (((parameterDimension z+parameterBinaryLength z)+parameterAccuracy z),1)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_composition (f := fun z : SamplingParameters => ((parameterDimension z+parameterBinaryLength z),parameterAccuracy z)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_composition (f := fun z : SamplingParameters => (parameterDimension z,parameterBinaryLength z)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_parameterDimension) (polynomial_parameterBinaryLength)) polynomial_add) (polynomial_parameterAccuracy)) polynomial_add) (polynomial_constant 1)) polynomial_add) polynomial_sixtySecondPower)) polynomial_multiply

def parameterWordCount (z : SamplingParameters) : ℕ := (parameterTrials z*((parameterSteps z*(parameterProposalWidth z+parameterCompletionWidth z))+parameterCompletionWidth z))

def parameterWordCountRealizer : Realizer parameterWordCount :=
  composition (f := fun z : SamplingParameters => (parameterTrials z,((parameterSteps z*(parameterProposalWidth z+parameterCompletionWidth z))+parameterCompletionWidth z))) (g := fun t : ℕ×ℕ => t.1*t.2) (pair (parameterTrialsRealizer) (composition (f := fun z : SamplingParameters => ((parameterSteps z*(parameterProposalWidth z+parameterCompletionWidth z)),parameterCompletionWidth z)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (composition (f := fun z : SamplingParameters => (parameterSteps z,(parameterProposalWidth z+parameterCompletionWidth z))) (g := fun t : ℕ×ℕ => t.1*t.2) (pair (parameterStepsRealizer) (composition (f := fun z : SamplingParameters => (parameterProposalWidth z,parameterCompletionWidth z)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (parameterProposalWidthRealizer) (parameterCompletionWidthRealizer)) add)) multiply) (parameterCompletionWidthRealizer)) add)) multiply

theorem polynomial_parameterWordCount : PolynomialTime parameterWordCountRealizer :=
  polynomial_composition (f := fun z : SamplingParameters => (parameterTrials z,((parameterSteps z*(parameterProposalWidth z+parameterCompletionWidth z))+parameterCompletionWidth z))) (g := fun t : ℕ×ℕ => t.1*t.2) (polynomial_pair (polynomial_parameterTrials) (polynomial_composition (f := fun z : SamplingParameters => ((parameterSteps z*(parameterProposalWidth z+parameterCompletionWidth z)),parameterCompletionWidth z)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_composition (f := fun z : SamplingParameters => (parameterSteps z,(parameterProposalWidth z+parameterCompletionWidth z))) (g := fun t : ℕ×ℕ => t.1*t.2) (polynomial_pair (polynomial_parameterSteps) (polynomial_composition (f := fun z : SamplingParameters => (parameterProposalWidth z,parameterCompletionWidth z)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_parameterProposalWidth) (polynomial_parameterCompletionWidth)) polynomial_add)) polynomial_multiply) (polynomial_parameterCompletionWidth)) polynomial_add)) polynomial_multiply

end ContingencyTables.ProfilePrograms

end OAI
