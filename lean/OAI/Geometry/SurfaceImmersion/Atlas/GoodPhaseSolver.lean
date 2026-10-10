import OAI.Geometry.SurfaceImmersion.Atlas.GoodPhaseCover
import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedGeometricSolver

namespace OAI

/-! Actual unit-scale linear metric solvers on the constructed good phase charts. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation

/-- Every compact target supported in a constructed good chart has the actual
unperturbed solver data required by the finite cancellation theorem. -/
theorem GoodPhaseChart.exists_unperturbed_solver
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (c : GoodPhaseChart (G ∘ planeCoordinateIsometry.symm) (coordinatePhase φ))
    (K : Compacts JetPolynomial.Base)
    (hK : (modeSupport K : Set SmallModes.Base) ⊆ c.chart.source) :
    ∃ d : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K 1 1,
      d.e = c.chart ∧ (∀ m, d.D m = 0) :=
  geometric_unperturbed_solver hG K hφ c.chart c.smooth c.smoothInverse hK
    (fun x _ => c.phase x) c.sourceCompact.isCompact c.targetCompact.isCompact
    c.sourceBound c.targetBound c.targetInside c.good

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
