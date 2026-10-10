import OAI.Geometry.RCD.Metric.ConvexPackingDimension
import OAI.Geometry.RCD.Sobolev.FiniteSpanOfIndependentBound

namespace OAI

/-! # Finite dimension of a spanning convex set with exact packing growth -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_dimensional_of_convex_packing {K : Set E} (hK : Convex ℝ K) (h0 : 0 ∈ K)
    (hspan : Submodule.span ℝ K = ⊤) (n : ℕ) (M : ℝ)
    (hpack : ∀ {ι : Type} [Fintype ι] (v : ι → E) {d : ℝ}, 0 < d → d ≤ 1 →
      (∀ i, v i ∈ K) → Pairwise (fun i j => d ≤ dist (v i) (v j)) →
      (Fintype.card ι:ℝ)*(d/2)^n ≤ M) :
    FiniteDimensional ℝ E ∧ Module.finrank ℝ E ≤ n :=
  finite_span_of_independent_bound K n hspan
    (fun v hv => convex_packing_no_extra_direction hK h0 n M hpack v hv)

end RegularPointCoordinates

end

end OAI
