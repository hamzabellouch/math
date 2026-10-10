import OAI.Analysis.Triangular.Certificate.ResidualPlus00
import OAI.Analysis.Triangular.Certificate.ResidualPlus01
import OAI.Analysis.Triangular.Certificate.ResidualPlus02
import OAI.Analysis.Triangular.Certificate.ResidualPlus03
import OAI.Analysis.Triangular.Certificate.ResidualPlus04
import OAI.Analysis.Triangular.Certificate.ResidualPlus05
import OAI.Analysis.Triangular.Certificate.ResidualPlus06
import OAI.Analysis.Triangular.Certificate.ResidualPlus07
import OAI.Analysis.Triangular.Certificate.ResidualPlus08
import OAI.Analysis.Triangular.Certificate.ResidualPlus09
import OAI.Analysis.Triangular.Certificate.ResidualPlus10
import OAI.Analysis.Triangular.Certificate.ResidualPlus11
import OAI.Analysis.Triangular.Certificate.ResidualPlus12
import OAI.Analysis.Triangular.Certificate.ResidualPlus13
import OAI.Analysis.Triangular.Certificate.ResidualPlus14
import OAI.Analysis.Triangular.Certificate.ResidualPlus15
import OAI.Analysis.Triangular.Certificate.ResidualPlus16
import OAI.Analysis.Triangular.Certificate.ResidualPlus17
import OAI.Analysis.Triangular.Certificate.ResidualPlus18
import OAI.Analysis.Triangular.Certificate.ResidualPlus19

namespace OAI

namespace AtomicTriangular.FiniteCertificate.AtomicMatrix

open AtomicTriangular.Interval

theorem residualPlus_bound (j : Fin 20) :
    matrixColBound (residual 0) j ≤ plusEpsilonNumerator := by
  fin_cases j
  · exact residualPlus00_bound
  · exact residualPlus01_bound
  · exact residualPlus02_bound
  · exact residualPlus03_bound
  · exact residualPlus04_bound
  · exact residualPlus05_bound
  · exact residualPlus06_bound
  · exact residualPlus07_bound
  · exact residualPlus08_bound
  · exact residualPlus09_bound
  · exact residualPlus10_bound
  · exact residualPlus11_bound
  · exact residualPlus12_bound
  · exact residualPlus13_bound
  · exact residualPlus14_bound
  · exact residualPlus15_bound
  · exact residualPlus16_bound
  · exact residualPlus17_bound
  · exact residualPlus18_bound
  · exact residualPlus19_bound

end AtomicTriangular.FiniteCertificate.AtomicMatrix

end OAI
