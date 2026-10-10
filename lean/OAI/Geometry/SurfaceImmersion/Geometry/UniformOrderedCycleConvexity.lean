import OAI.Geometry.SurfaceImmersion.Primitive.CircularCycleMetrics
import OAI.Geometry.SurfaceImmersion.Geometry.UniformCycleConvexity

namespace OAI

/-! The preselected convex phases apply to the actual ordered prefix metrics. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

 theorem uniform_ordered_cycle_convexity (m : ℕ)
    (g : SmoothMetric M) {c C K : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    ∃ L r : ℝ, 0 < L ∧ 0 < r ∧ ∀ D : ℝ, 0 ≤ D →
      ∃ N : ℕ, 0 < N ∧ ∀ (g₀ : SmoothMetric M),
        (∀ p v, c*g.inner p v v ≤ g₀.inner p v v) →
        ∀ (u : ∀ p : M, CovariantTwoTensor p)
          (f : Fin N → SmoothPrimitiveFamily (Fin m) u),
          (∀ k a, A.TensorWeightedBound 1 1 D ((f k).term a)) →
          (∀ k : Fin N, A.TensorWeightedBound 1 1 C (g₀.inner+((k.val : ℝ)/(N : ℝ)) • u)) →
          ∀ d : CircularPrimitiveFamily A (Fin (N*m)),
            (∀ a p, d.amplitude a p = (f a.divNat).cycleAmplitude N a.modNat p) →
            (∀ a, d.phase a = (f a.divNat).phase a.modNat) →
            (∀ a, d.convexPart a = L) → (∀ a, ‖d.linearPart a‖ ≤ K) →
            (∀ a, d.chartRadius a ≤ r) →
            ∀ a, d.ConvexMetric (d.prefixMetric g₀ a.castSucc) a := by
  obtain ⟨L,r,hL,hr,hchoose⟩ := A.uniform_cycle_convexity (ι := Fin m) g hc hC hK houter
  refine ⟨L,r,hL,hr,?_⟩
  intro D hD
  obtain ⟨N,hN,hconvex⟩ := hchoose D hD
  refine ⟨N,hN,?_⟩
  intro g₀ hlower u f hb hpath d ha hp hLpart hlinear hradius a
  obtain ⟨⟨k,j⟩,rfl⟩ := finProdFinEquiv.surjective a
  change ∀ p ∈ tsupport (A.weight (d.curves (finProdFinEquiv (k,j))).index),
    ‖coordinateChart ((d.curves (finProdFinEquiv (k,j))).index : M) p-
      coordinateChart ((d.curves (finProdFinEquiv (k,j))).index : M) (d.curves (finProdFinEquiv (k,j))).index‖ ≤ _ →
    ∀ v : Base, v ≠ 0 → _
  intro p hpa hpr v hv
  rw [d.prefixMetric_cycle f ha hp g₀ k j,hLpart]
  have hbound := hconvex g₀ hlower u (f k) (hb k) k.val
    (CircularPrimitiveFamily.prefixIndices j.castSucc) (hpath k)
    (d.curves (finProdFinEquiv (k,j))).index p hpa (hpr.trans (hradius _))
    (d.linearPart (finProdFinEquiv (k,j))) (hlinear _) v
  have hsq : 0 < v.1^2+v.2^2 := by
    by_contra hn
    have h1 : v.1 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg v.2])
    have h2 : v.2 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg v.1])
    exact hv (Prod.ext h1 h2)
  exact (mul_pos (half_pos hL) hsq).trans_le hbound

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
