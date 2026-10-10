import OAI.Geometry.IsometricImmersion.Flows.ActualFlowHighEquation
import OAI.Geometry.IsometricImmersion.Immersions.HeightCoefficientRegularity

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry

theorem heightOriginalC0_contDiffOn {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (ell : ℕ) :
    ContDiffOn ℝ ∞ (heightOriginalC0 g z ell) U := by
  have hq := hessianQuotient_contDiffOn hg hU hz hyy
  exact (((coordinateDrift_contDiffOn hq hq hU).sub
    (hq.mul (heightPFirst_contDiffOn hg hU hz hyy 0))).sub
      (heightPFirst_contDiffOn hg hU hz hyy 1)).add
        (contDiffOn_const.mul (partial_contDiffOn (heightOriginalA_contDiffOn hg hU hz hyy) hU 1))

theorem driftOperator_contDiffOn {q A B C u : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U) (hA : ContDiffOn ℝ ∞ A U)
    (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (driftOperator q A B C u) U := by
  have hDu := coordinateDrift_contDiffOn hq hu hU
  exact (((coordinateDrift_contDiffOn hq hDu hU).add
    (hA.mul (partial_contDiffOn (partial_contDiffOn hu hU 1) hU 1))).add
      (hB.mul hDu)).add (hC.mul (partial_contDiffOn hu hU 1))

end SmoothLocal.Flow

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow

theorem actualHighRemainder_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (m : ℕ) :
    ContDiffOn ℝ ∞ (actualHighRemainder g z m) U := by
  have hh := driftOperator_contDiffOn hU (hessianQuotient_contDiffOn hg hU hz hyy)
    (heightOriginalA_contDiffOn hg hU hz hyy) (heightOriginalB_contDiffOn hg hU hz hyy (m+3))
    (heightOriginalC0_contDiffOn hg hU hz hyy (m+3)) (verticalJet_contDiffOn hU hz (m+3))
  exact hh.congr (fun p hp => (actual_differentiated_drift hg hU hz hD hyy m hp).symm)

end SmoothLocal.HighEquation

end

end OAI
