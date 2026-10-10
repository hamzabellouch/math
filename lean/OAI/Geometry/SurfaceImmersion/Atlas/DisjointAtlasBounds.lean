import OAI.Geometry.SurfaceImmersion.Geometry.DisjointJetBounds
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasWeightedBounds

namespace OAI

/-! The fixed atlas retains the count-free estimate for a disjoint family
of local corrections. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem disjoint_weighted_sum_bound {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q : ι → M → Space) (hq : ∀ i ∈ s, ContMDiff planeModel spaceModel ∞ (q i))
    (hdisj : (↑s : Set ι).Pairwise fun i j => Disjoint (tsupport (q i)) (tsupport (q j)))
    {C : ℝ} (hC : 0 ≤ C) {m : ℕ}
    (hb : ∀ i ∈ s, A.WeightedBound 1 m C (q i)) :
    A.WeightedBound 1 m C (∑ i ∈ s, q i) := by
  intro a
  rw [localize_sum]
  have hloc : (↑s : Set ι).Pairwise fun i j =>
      Disjoint (tsupport (localize (a : M) (A.weight a) (q i)))
        (tsupport (localize (a : M) (A.weight a) (q j))) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨p,⟨hp,hpi⟩,hpx⟩ := localize_tsupport_inter (a : M) (A.weight_support a) (q i) hxi
    obtain ⟨r,⟨hr,hrj⟩,hrx⟩ := localize_tsupport_inter (a : M) (A.weight_support a) (q j) hxj
    have hpr : p = r := (chart (a : M)).injOn (A.weight_support a hp)
      (A.weight_support a hr) (hpx.trans hrx.symm)
    exact Set.disjoint_left.mp (hdisj hi hj hij) hpi (hpr.symm ▸ hrj)
  exact SphericalJets.disjoint_sum_weighted_bound s
    (fun i => localize (a : M) (A.weight a) (q i))
    (fun i hi => localize_smooth (a : M) (A.weight_smooth a) (A.weight_support a) (hq i hi))
    hloc hC (fun i hi => hb i hi a)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
