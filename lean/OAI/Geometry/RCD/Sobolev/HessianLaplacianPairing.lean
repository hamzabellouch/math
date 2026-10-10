import OAI.Geometry.RCD.Sobolev.HessianActionIntegral

namespace OAI

/-! # The integrated Hessian action in weak Laplacian pairings

This is integration by parts in the three-term Hessian formula. It needs
only the actual L2 weak Laplacians and the three Sobolev Gram representatives.
-/

open MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
theorem integral_hessian_laplacian_pairings
    (w u v wu wv uv : SobolevSpace μ Q) (q d e : Lp ℝ 2 μ)
    (hw : IsWeakLaplacian μ Q w q) (hu : IsWeakLaplacian μ Q u d)
    (hv : IsWeakLaplacian μ Q v e) :
    (∫ x, localHessianAction μ Q w u v wu wv uv x ∂μ) =
      (-inner ℝ d (SobolevSpace.toLp μ Q wv)-inner ℝ e (SobolevSpace.toLp μ Q wu)+
        inner ℝ q (SobolevSpace.toLp μ Q uv))/2 := by
  rw [integral_localHessianAction,hu,hv,hw]
  ring

end RegularPointCoordinates

end

end OAI
