import OAI.Geometry.RCD.Coordinates.RegularLimitMidpointGeometry
import OAI.Geometry.RCD.Transport.LocalHilbertEmbedding

namespace OAI

/-! # Inner-product balls obtained from the original near-regular RCD sequence -/

open Set Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [MetricSpace Y] [ProperSpace Y] {K : ℝ} {n : ℕ}
  (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]

include hX in
theorem regular_limit_inner_product_ball (hn : 2 ≤ n) (hK : K ≤ 0)
    {o : X} (ho : IsRegular n o) {q : Y}
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hp : Tendsto p atTop (𝓝 o)) (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -1 ≤ K * (4 * r k)^2)
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) 5 (ε k) (V k)) :
    ∃ (E : Type v) (m : NormedAddCommGroup E),
      letI := m
      ∃ (_ : InnerProductSpace ℝ E) (f : closedBall q (1/4:ℝ) → E),
        Isometry f ∧ Convex ℝ (range f) ∧ IsCompact (range f) ∧
          Submodule.span ℝ (range f) = ⊤ ∧ f ⟨q,by simp⟩ = 0 := by
  obtain ⟨G⟩ := hX.regular_limit_midpoint_geometry hn hK ho p r ε V hp hr hr0 hε hcurv hV
  exact G.exists_local_inner_product_embedding

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
