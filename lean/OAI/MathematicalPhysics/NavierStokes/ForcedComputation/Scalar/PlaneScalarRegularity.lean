import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarGlobal

namespace OAI

/-! Finite-slab spatial derivative bounds for the unique scalar solution. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem PlaneSpatialBounds.restrict {T S : ℝ} {w : ℝ → Plane → ℝ}
    (hw : PlaneSpatialBounds T w) (hST : S ≤ T) : PlaneSpatialBounds S w := by
  obtain ⟨B, hB⟩ := hw
  exact ⟨B, fun t ht => hB t ⟨ht.1, ht.2.trans hST⟩⟩

theorem PlaneSpatialBounds.congr {T : ℝ} {w v : ℝ → Plane → ℝ}
    (hw : PlaneSpatialBounds T w) (he : ∀ t ∈ Icc 0 T, v t = w t) :
    PlaneSpatialBounds T v := by
  obtain ⟨B, hB⟩ := hw
  refine ⟨B, ?_⟩
  intro t ht k hk x
  rw [he t ht]
  exact hB t ht k hk x

theorem PlaneScalarSolution.spatial_bounds (hE : PlaneScalarExistence)
    {T ν : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 ≤ T) (hν : 0 < ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h) :
    PlaneSpatialBounds T w := by
  obtain ⟨v, hv, hb⟩ := hE (T + 1) ν (by linarith) hν a h ha hh hc
  have hST : T ≤ T + 1 := by linarith
  have he := hw.unique (hv.restrict hST) hT hν.le ha hc
  exact (hb.restrict hST).congr he

end ForcedComputation.VelocityDetector

end

end OAI
