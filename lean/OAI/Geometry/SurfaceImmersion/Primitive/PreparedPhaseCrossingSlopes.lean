import OAI.Geometry.SurfaceImmersion.Primitive.GenericPhaseCrossing
import OAI.Geometry.SurfaceImmersion.Primitive.FiniteBoundaryCrossingSets
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseCurvePairGeometry

namespace OAI

/-! The generic phase selection makes each relevant transported boundary
direction nonvertical, and a finite crossing set has a fixed slope bound. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {B : SmoothingAtlas M}
namespace PhaseBoundaryCurve

lemma directionIn_first_ne_of_covectors (c d : PhaseBoundaryCurve B)
    (q : M) (phi psi : M → ℝ)
    (hc : ∀ p, (surfacePhaseChart (c.index : M) c.phase p).1 = phi p)
    (hd : ∀ p, (surfacePhaseChart (d.index : M) d.phase p).1 = psi p)
    {p : M} (hq : p ∈ (coordinateChart q).source)
    (hp : p ∈ c.carrier) (hps : p ∈ (surfacePhaseChart (d.index : M) d.phase).source)
    (hind : covectorDet
      (phaseDerivative (phi ∘ (coordinateChart q).symm) (coordinateChart q p))
      (phaseDerivative (psi ∘ (coordinateChart q).symm) (coordinateChart q p)) ≠ 0) :
    (c.directionIn d p).1 ≠ 0 :=
  generic_phase_crossing_first_nonzero q (c.index : M) (d.index : M)
    c.phase d.phase c.smooth c.inverse_smooth d.smooth
    phi psi hc hd hq (c.source hp) hps hind

end PhaseBoundaryCurve

lemma finite_crossing_slope_bound {σ : Type*} [Fintype σ]
    (v w : σ → Base) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ j, |(v j).2/(v j).1| ≤ L ∧ |(w j).2/(w j).1| ≤ L := by
  classical
  let L := ∑ j, (|(v j).2/(v j).1| + |(w j).2/(w j).1|)
  have hnon (j : σ) : 0 ≤ |(v j).2/(v j).1| + |(w j).2/(w j).1| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨L,Finset.sum_nonneg (fun j _ => hnon j),?_⟩
  intro j
  have hj : |(v j).2/(v j).1| + |(w j).2/(w j).1| ≤ L :=
    Finset.single_le_sum (fun k _ => hnon k) (Finset.mem_univ j)
  exact ⟨(le_add_of_nonneg_right (abs_nonneg _)).trans hj,
    (le_add_of_nonneg_left (abs_nonneg _)).trans hj⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
