import OAI.Geometry.SurfaceImmersion.Whitney.CompactDoublePairs
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapAxisCoordinates

namespace OAI

/-! Away from zero, the opposite kernel-axis source points form genuine
double pairs of the original surface map throughout the chart domain. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}
namespace SurfaceCrosscapCoordinates

theorem axis_double_pair (c : SurfaceCrosscapCoordinates f p) {u : ℝ} (hu : u ≠ 0)
    (hplus : crosscapAxis u ∈ c.source.target) (hminus : crosscapAxis (-u) ∈ c.source.target) :
    (c.axisCurve u,c.axisCurve (-u)) ∈ surfaceDoublePairs f := by
  have hp : c.axisCurve u ∈ c.source.source := c.source.map_target hplus
  have hm : c.axisCurve (-u) ∈ c.source.source := c.source.map_target hminus
  have hpc : c.source (c.axisCurve u) = crosscapAxis u := c.source.right_inv hplus
  have hmc : c.source (c.axisCurve (-u)) = crosscapAxis (-u) := c.source.right_inv hminus
  constructor
  · intro he
    have hv := congrArg (fun x => c.source x 1) he
    rw [hpc,hmc,crosscapAxis_apply,crosscapAxis_apply] at hv
    simp only [Matrix.cons_val_one,Matrix.cons_val_zero] at hv
    exact hu (by linarith)
  · rw [c.model_eq _ hp,c.model_eq _ hm,hpc,hmc]
    congr 1
    rw [crosscapAxis_apply,crosscapAxis_apply]
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [standardCrosscap]
    · simp [standardCrosscap]

end SurfaceCrosscapCoordinates
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
