import OAI.Analysis.Triangular.Certificate.ResidualMinus00
import OAI.Analysis.Triangular.Certificate.ResidualMinus01
import OAI.Analysis.Triangular.Certificate.ResidualMinus02
import OAI.Analysis.Triangular.Certificate.ResidualMinus03
import OAI.Analysis.Triangular.Certificate.ResidualMinus04
import OAI.Analysis.Triangular.Certificate.ResidualMinus05
import OAI.Analysis.Triangular.Certificate.ResidualMinus06
import OAI.Analysis.Triangular.Certificate.ResidualMinus07
import OAI.Analysis.Triangular.Certificate.ResidualMinus08
import OAI.Analysis.Triangular.Certificate.ResidualMinus09
import OAI.Analysis.Triangular.Certificate.ResidualMinus10
import OAI.Analysis.Triangular.Certificate.ResidualMinus11
import OAI.Analysis.Triangular.Certificate.ResidualMinus12
import OAI.Analysis.Triangular.Certificate.ResidualMinus13
import OAI.Analysis.Triangular.Certificate.ResidualMinus14
import OAI.Analysis.Triangular.Certificate.ResidualMinus15
import OAI.Analysis.Triangular.Certificate.ResidualMinus16
import OAI.Analysis.Triangular.Certificate.ResidualMinus17
import OAI.Analysis.Triangular.Certificate.ResidualMinus18
import OAI.Analysis.Triangular.Certificate.ResidualMinus19

namespace OAI

namespace AtomicTriangular.FiniteCertificate.AtomicMatrix
open AtomicTriangular.Interval

theorem residualMinus_bound (j : Fin 20) :
    matrixColBound (residual 1) j ≤ minusEpsilonNumerator := by
  fin_cases j
  · exact residualMinus00_bound
  · exact residualMinus01_bound
  · exact residualMinus02_bound
  · exact residualMinus03_bound
  · exact residualMinus04_bound
  · exact residualMinus05_bound
  · exact residualMinus06_bound
  · exact residualMinus07_bound
  · exact residualMinus08_bound
  · exact residualMinus09_bound
  · exact residualMinus10_bound
  · exact residualMinus11_bound
  · exact residualMinus12_bound
  · exact residualMinus13_bound
  · exact residualMinus14_bound
  · exact residualMinus15_bound
  · exact residualMinus16_bound
  · exact residualMinus17_bound
  · exact residualMinus18_bound
  · exact residualMinus19_bound

end AtomicTriangular.FiniteCertificate.AtomicMatrix

end OAI
