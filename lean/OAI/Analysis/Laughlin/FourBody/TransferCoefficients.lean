import OAI.Analysis.Laughlin.FourBody.MiddleLimit
import OAI.Analysis.Laughlin.FourBody.TransferConjugation
import OAI.Analysis.Laughlin.Operators.CopyQuadraticMatrix
import OAI.Analysis.Laughlin.Operators.MatrixMetricError

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter Spin

noncomputable def finiteLocalFourMatrix (Q D : ℕ) : LocalFourIndex D → LocalFourIndex D → ℝ :=
  copyQuadraticMatrix (finiteFourMiddle Q D)
    (fun i b => physicalFourBeta Q (Certificate.copyLabel i) D b)

noncomputable def limitLocalFourMatrix (D : ℕ) : LocalFourIndex D → LocalFourIndex D → ℝ :=
  copyQuadraticMatrix (limitFourMiddle D)
    (fun i b => fourBodyLimitCoefficient (Certificate.copyLabel i) D D
      b.val.1.val b.val.2.1.val b.val.2.2.val)

theorem finiteLocalFourMatrix_tendsto (D : ℕ) (a b : LocalFourIndex D) :
    Tendsto (fun Q => finiteLocalFourMatrix Q D a b) atTop (𝓝 (limitLocalFourMatrix D a b)) := by
  unfold finiteLocalFourMatrix limitLocalFourMatrix copyQuadraticMatrix
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  have hiD : Certificate.copyLabel i ≤ D := by unfold Certificate.copyLabel; have := i.isLt; omega
  have hjD : Certificate.copyLabel j ≤ D := by unfold Certificate.copyLabel; have := j.isLt; omega
  exact ((finiteFourMiddle_tendsto D i j).mul (physicalFourBeta_tendsto _ D hiD a)).mul
    (physicalFourBeta_tendsto _ D hjD b)

noncomputable def fourBodyRho (D Q : ℕ) : ℝ :=
  matrixMetricError 24 Q (finiteLocalFourMatrix Q D) (limitLocalFourMatrix D) *
    (Fintype.card (LocalFourIndex D) : ℝ)^2

theorem fourBodyRho_nonneg (D Q : ℕ) : 0 ≤ fourBodyRho D Q :=
  mul_nonneg (matrixMetricError_nonneg _ _ _ _) (sq_nonneg _)

theorem fourBodyRho_tendsto (D : ℕ) : Tendsto (fourBodyRho D) atTop (𝓝 0) := by
  have h := (matrixMetricError_tendsto 24 (fun Q => finiteLocalFourMatrix Q D)
    (limitLocalFourMatrix D) (finiteLocalFourMatrix_tendsto D)).mul_const
      ((Fintype.card (LocalFourIndex D) : ℝ)^2)
  change Tendsto (fun Q => matrixMetricError 24 Q (finiteLocalFourMatrix Q D)
    (limitLocalFourMatrix D) * (Fintype.card (LocalFourIndex D) : ℝ)^2) atTop (𝓝 0)
  simpa using h

end Laughlin.Fock

end OAI
