import OAI.Combinatorics.ContingencyTables.Sampling.OuterTableProgram

namespace OAI

/-! # Preparing the original-table return from a residual draw -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

abbrev OuterTrialInput := (ProfileCheckData×ℕ)×MatrixCode

def outputLargeRows (z : OuterTrialInput) : List ℕ := largeIndices (z.1.1.2,z.1.1.1.2.1)
def outputLargeColumns (z : OuterTrialInput) : List ℕ := largeIndices (z.1.1.2,z.1.1.1.2.2)

def outputLargeRowsRealizer : Realizer outputLargeRows :=
  composition (pair (composition (composition first first) second)
    (composition (composition (composition (composition first first) first) second) first))
    largeIndicesRealizer
def outputLargeColumnsRealizer : Realizer outputLargeColumns :=
  composition (pair (composition (composition first first) second)
    (composition (composition (composition (composition first first) first) second) second))
    largeIndicesRealizer

theorem polynomial_outputLargeRows : PolynomialTime outputLargeRowsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
      polynomial_first)) polynomial_largeIndices
theorem polynomial_outputLargeColumns : PolynomialTime outputLargeColumnsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
      polynomial_second)) polynomial_largeIndices

def outputData (z : OuterTrialInput) : OuterTableData :=
  ((z.1.1.1.1,(outputLargeRows z,outputLargeColumns z)),((z.1.1.2,z.1.2),z.2))
def outputDataRealizer : Realizer outputData :=
  pair (pair (composition (composition (composition first first) first) first)
      (pair outputLargeRowsRealizer outputLargeColumnsRealizer))
    (pair (pair (composition (composition first first) second) (composition first second)) second)

theorem polynomial_outputData : PolynomialTime outputDataRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_pair polynomial_outputLargeRows polynomial_outputLargeColumns))
    (polynomial_pair (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_composition polynomial_first polynomial_second)) polynomial_second)

def prepareOutput (z : OuterTrialInput) : OuterMatrixInput := (z.1.1.1.2,outputData z)
def prepareOutputRealizer : Realizer prepareOutput :=
  pair (composition (composition (composition first first) first) second) outputDataRealizer

theorem polynomial_prepareOutput : PolynomialTime prepareOutputRealizer :=
  polynomial_pair (polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
    polynomial_outputData

def outerTrial (z : OuterTrialInput) : Option MatrixCode := acceptedTable (prepareOutput z)
def outerTrialRealizer : Realizer outerTrial :=
  composition prepareOutputRealizer acceptedTableRealizer

theorem polynomial_outerTrial : PolynomialTime outerTrialRealizer :=
  polynomial_composition polynomial_prepareOutput polynomial_acceptedTable

end ContingencyTables.ProfilePrograms

end OAI
