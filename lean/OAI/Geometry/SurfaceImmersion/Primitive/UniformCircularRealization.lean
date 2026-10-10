import OAI.Geometry.SurfaceImmersion.Geometry.UniformOrderedCycleConvexity
import OAI.Geometry.SurfaceImmersion.Geometry.UniformCycleConvexity

namespace OAI

/-! The preselected convex phases apply to the actual ordered prefix metrics. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

 theorem uniform_circular_realization (m : ℕ)
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
            ∀ (h : SmoothMetric M), h.inner = g₀.inner+u →
              ∀ (F : M → Space) (n : PreferredNormal F),
                IsSmoothIsometricImmersion M g₀ F → MetricGoodPhaseData g₀ F →
                FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) F n →
                ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧
                  Nonempty (MetricGoodPhaseData h W) := by
  obtain ⟨L,r,hL,hr,hchoose⟩ := A.uniform_ordered_cycle_convexity m g hc hC hK houter
  refine ⟨L,r,hL,hr,?_⟩
  intro D hD
  obtain ⟨N,hN,hcv⟩ := hchoose D hD
  refine ⟨N,hN,?_⟩
  intro g₀ hlower u f hb hpath d ha hp hLpart hlinear hradius h htarget F n hF data hgeom
  have hconvex := hcv g₀ hlower u f hb hpath d ha hp hLpart hlinear hradius
  apply d.realize_total g₀ h _ hconvex n hF data hgeom
  rw [d.totalTensor_cycle f ha hp hN]
  exact htarget

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
