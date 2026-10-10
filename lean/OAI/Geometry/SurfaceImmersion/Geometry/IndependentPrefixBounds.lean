import OAI.Geometry.SurfaceImmersion.Primitive.CircularCycleMetrics
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveCycleBounds

namespace OAI

/-! Bounds for ordered prefixes in the original atlas, independently of
the atlas that describes the geometric primitive disks. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem independent_prefix_bounds (m : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ N : ℕ, 0 < N ∧ ∀ (B : SmoothingAtlas M) (g g₀ : SmoothMetric M)
      (c C : ℝ), (∀ p v, c*g.inner p v v ≤ g₀.inner p v v) →
      ∀ (u : ∀ p : M, CovariantTwoTensor p)
        (f : Fin N → SmoothPrimitiveFamily (Fin m) u),
      (∀ k a, A.TensorWeightedBound 1 1 D ((f k).term a)) →
      (∀ k : Fin N, A.TensorWeightedBound 1 1 C (g₀.inner+((k.val : ℝ)/(N : ℝ)) • u)) →
      ∀ d : CircularPrimitiveFamily B (Fin (N*m)),
      (∀ a p, d.amplitude a p = (f a.divNat).cycleAmplitude N a.modNat p) →
      (∀ a, d.phase a = (f a.divNat).phase a.modNat) →
      ∀ a : Fin (N*m), A.TensorWeightedBound 1 1 (C+1) (d.prefixMetric g₀ a.castSucc).inner ∧
        ∀ p v, c*g.inner p v v ≤ (d.prefixMetric g₀ a.castSucc).inner p v v := by
  obtain ⟨N,hN,hcount⟩ := SmoothPrimitiveFamily.exists_cycle_count (ι := Fin m) D
  refine ⟨N,hN,?_⟩
  intro B g g₀ c C hlower u f hb hpath d ha hp a
  obtain ⟨⟨k,j⟩,rfl⟩ := finProdFinEquiv.surjective a
  rw [d.prefixMetric_cycle f ha hp g₀ k j]
  have he : (f k).cycleMetric B g₀ N k.val (CircularPrimitiveFamily.prefixIndices j.castSucc) =
      (f k).cycleMetric A g₀ N k.val (CircularPrimitiveFamily.prefixIndices j.castSucc) :=
    metric_eq_of_inner_eq rfl
  rw [he]
  refine ⟨?_,?_⟩
  · have hh := (f k).cycleMetric_bound A hD 1 (hb k) g₀ N k.val
      (CircularPrimitiveFamily.prefixIndices j.castSucc) (hpath k)
    intro i
    apply (hh i).mono_const
    simpa only [Fintype.card_fin] using add_le_add_right hcount C
  · intro p v
    exact (hlower p v).trans ((f k).cycleMetric_lower A g₀ N k.val
      (CircularPrimitiveFamily.prefixIndices j.castSucc) p v)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
