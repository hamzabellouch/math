import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveCycleBounds
import OAI.Geometry.SurfaceImmersion.Atlas.UniformAtlasConvexPhases

namespace OAI

/-! Choose convex phases first, then choose the number of cycles from a
uniform primitive budget. Every partial metric has the required positive
Hessian, including when the primitive family differs between cycles. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_cycle_convexity {ι : Type*} [Fintype ι]
    (g : SmoothMetric M) {c C K : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    ∃ L r : ℝ, 0 < L ∧ 0 < r ∧ ∀ D : ℝ, 0 ≤ D →
      ∃ N : ℕ, 0 < N ∧ ∀ (g₀ : SmoothMetric M),
        (∀ p v, c*g.inner p v v ≤ g₀.inner p v v) →
        ∀ (u : ∀ p : M, CovariantTwoTensor p) (d : SmoothPrimitiveFamily ι u),
          (∀ a, A.TensorWeightedBound 1 1 D (d.term a)) →
          ∀ (k : ℕ) (s : Finset ι),
            A.TensorWeightedBound 1 1 C (g₀.inner+((k : ℝ)/(N : ℝ)) • u) →
            ∀ (i : A.centers) (p : M), p ∈ tsupport (A.weight i) →
              ‖coordinateChart (i : M) p-coordinateChart (i : M) (i : M)‖ ≤ r →
              ∀ ell : SmallModes.Base, ‖ell‖ ≤ K → ∀ v : SmallModes.Base,
                (L/2)*(v.1^2+v.2^2) ≤ coordinateMetricHessian
                  (coordinateMetric (d.cycleMetric A g₀ N k s) (i : M))
                  (centeredConvexPhase ell L (coordinateChart (i : M) (i : M)))
                  (coordinateChart (i : M) p) v v := by
  obtain ⟨L,r,hL,hr,hphase⟩ := A.uniform_atlas_convex_phases g hc
    (show 0 ≤ C+1 by linarith) hK houter
  refine ⟨L,r,hL,hr,fun D hD => ?_⟩
  obtain ⟨N,hN,hcount⟩ := SmoothPrimitiveFamily.exists_cycle_count (ι := ι) D
  refine ⟨N,hN,?_⟩
  intro g₀ hlower u d hb k s hpath i p hp hsmall ell hell v
  have hbudget := d.cycleMetric_bound A hD 1 hb g₀ N k s hpath
  have hbudget' : A.TensorWeightedBound 1 1 (C+1) (d.cycleMetric A g₀ N k s).inner := by
    intro j
    exact (hbudget j).mono_const (by linarith)
  have hlower' : ∀ q w, c*g.inner q w w ≤ (d.cycleMetric A g₀ N k s).inner q w w := by
    intro q w
    exact (hlower q w).trans (d.cycleMetric_lower A g₀ N k s q w)
  exact hphase _ hbudget' hlower' i p hp hsmall ell hell v

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
