import OAI.Combinatorics.ContingencyTables.Sampling.ProfileSamplingProgram

namespace OAI

/-! # The sampler's public binary parser and matrix printer -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralParse MatchingFPRAS.LiteralCodec
open DensePrograms

/-- Safely locate the precision field after the two margin vectors. -/
def samplingPrecision (ns : List ℕ) : ℕ :=
  (ns.drop (2+ns.headD 0+ns.tail.headD 0)).headD 0

def samplingPrecisionRealizer : Realizer samplingPrecision := by
  let M : Realizer (fun ns : List ℕ => ns.headD 0) := head 0
  let N : Realizer (fun ns : List ℕ => ns.tail.headD 0) := composition tail (head 0)
  let offset : Realizer (fun ns : List ℕ => 2+ns.headD 0+ns.tail.headD 0) :=
    composition (pair (composition (pair (constant 2) M) add) N) add
  exact composition (composition (pair identity offset) dropFast) (head 0)

theorem polynomial_samplingPrecision : PolynomialTime samplingPrecisionRealizer := by
  unfold samplingPrecisionRealizer
  exact polynomial_composition (polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair (polynomial_constant 2) (polynomial_head 0))
        polynomial_add)
      (polynomial_composition polynomial_tail (polynomial_head 0))) polynomial_add))
    polynomial_dropFast) (polynomial_head 0)

def samplingInput (ns : List ℕ) : SamplingParameters :=
  (GreedyFeasibleTable.marginLists ns,samplingPrecision ns)

def samplingInputRealizer : Realizer samplingInput :=
  pair GreedyFeasibleTable.marginListsRealizer samplingPrecisionRealizer

theorem polynomial_samplingInput : PolynomialTime samplingInputRealizer :=
  polynomial_pair GreedyFeasibleTable.polynomial_marginLists polynomial_samplingPrecision

def parsedSampling (as : List MatchingFPRAS.Symbol) : SamplingParameters := samplingInput (parse as)
def parsedSamplingRealizer : Realizer parsedSampling := composition (f := parse) (g := samplingInput) parseRealizer samplingInputRealizer

theorem polynomial_parsedSampling : PolynomialTime parsedSamplingRealizer :=
  polynomial_composition polynomial_parse polynomial_samplingInput

def publicWordCount (as : List MatchingFPRAS.Symbol) : ℕ := parameterWordCount (parsedSampling as)
def publicWordCountRealizer : Realizer publicWordCount :=
  composition (f := parsedSampling) (g := parameterWordCount) parsedSamplingRealizer parameterWordCountRealizer

theorem polynomial_publicWordCount : PolynomialTime publicWordCountRealizer :=
  polynomial_composition polynomial_parsedSampling polynomial_parameterWordCount

def publicSampling (z : List MatchingFPRAS.Symbol×List Bool) : List MatchingFPRAS.Symbol :=
  GreedyFeasibleTable.printMatrix (samplingMatrix (parsedSampling z.1,z.2))

def publicSamplingRealizer : Realizer publicSampling :=
  composition
    (f := fun z : List MatchingFPRAS.Symbol×List Bool => samplingMatrix (parsedSampling z.1,z.2))
    (g := GreedyFeasibleTable.printMatrix)
    (composition (f := fun z : List MatchingFPRAS.Symbol×List Bool => (parsedSampling z.1,z.2))
      (g := samplingMatrix) (pair (composition
        (f := fun z : List MatchingFPRAS.Symbol×List Bool => z.1) (g := parsedSampling)
        first parsedSamplingRealizer) second) samplingMatrixRealizer) GreedyFeasibleTable.printMatrixRealizer

theorem polynomial_publicSampling : PolynomialTime publicSamplingRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_parsedSampling) polynomial_second)
    polynomial_samplingMatrix) GreedyFeasibleTable.polynomial_printMatrix

end ContingencyTables.ProfilePrograms

end OAI
