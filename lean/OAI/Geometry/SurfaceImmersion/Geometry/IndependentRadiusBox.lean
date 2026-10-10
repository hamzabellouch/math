import OAI.Geometry.SurfaceImmersion.Atlas.IndependentShrinkingWeights
import OAI.Geometry.SurfaceImmersion.Atlas.ShrinkingAtlasWeightBounds

namespace OAI

/-! A fixed open radius box with uniform bounds for every independent
choice. The box and its derivative constants precede all later cycle counts. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]
variable {ι : Type*} [Fintype ι]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- All radii may be varied independently inside the displayed nonempty
open box. The actual weights remain uniformly close to their reference and
have one common finite-order atlas bound. -/
theorem independent_radius_box (index : ι → A.centers) (r0 : ι → ℝ)
    (hnon : ∀ a x, 0 ≤ A.weight (index a) x) (hr0 : ∀ a, 0 < r0 a)
    (hreg : ∀ a, circularCoordinateRegion (index a : M) (r0 a) ⊆
      (coordinateChart (index a : M)).target)
    (hpos : ∀ a x, 0 < A.weight (index a) x ↔
      x ∈ circularCoordinateDisk (index a : M) (r0 a))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ (delta : ℝ) (C : ℕ → ℝ), 0 < delta ∧ (∀ a, delta ≤ r0 a/2) ∧
      (∀ m, 0 ≤ C m) ∧ ∀ r : ι → ℝ,
      (∀ a, r0 a-delta < r a ∧ r a < r0 a-delta/2) →
      (∀ a, 0 < r a) ∧
      (∀ a, ContMDiff planeModel 𝓘(ℝ) ∞
        (shrinkingCircularWeight (index a : M) (A.weight (index a)) (r0 a) (r a))) ∧
      (∀ a x, 0 < shrinkingCircularWeight (index a : M) (A.weight (index a)) (r0 a) (r a) x ↔
        x ∈ circularCoordinateDisk (index a : M) (r a)) ∧
      (∀ a, tsupport (shrinkingCircularWeight (index a : M) (A.weight (index a)) (r0 a) (r a)) ⊆
        circularDiskClosure (index a : M) (r a)) ∧
      (∀ a x, |shrinkingCircularWeight (index a : M) (A.weight (index a)) (r0 a) (r a) x-
        A.weight (index a) x| < eps) ∧
      ∀ a m, A.WeightedBound 1 m (C m)
        (shrinkingCircularWeight (index a : M) (A.weight (index a)) (r0 a) (r a)) := by
  classical
  obtain ⟨delta,hdelta,hdeltaR,hnear⟩ := independent_shrinking_weights
    (fun a => (index a : M)) (fun a => A.weight (index a)) r0
    (fun a => A.weight_smooth (index a)) hnon hr0 hreg hpos heps
  have hR (a : ι) : (r0 a-delta/2)^2 < (r0 a)^2 := by
    have := hdeltaR a
    have := hr0 a
    nlinarith
  choose B hB hb using fun a => A.shrinking_weight_atlas_bounds (index a) (hreg a) (hR a)
  refine ⟨delta,fun m => ∑ a : ι, B a m,hdelta,hdeltaR,
    (fun m => Finset.sum_nonneg (fun a _ => hB a m)),?_⟩
  intro r hr
  have hr' : ∀ a, r0 a-delta < r a ∧ r a < r0 a := by
    intro a
    exact ⟨(hr a).1,lt_trans (hr a).2 (by linarith)⟩
  obtain ⟨hrpos,hsmooth,hpositive,hsupport,hclose⟩ := hnear r hr'
  refine ⟨hrpos,hsmooth,hpositive,hsupport,hclose,?_⟩
  intro a m
  have hr2 : (r a)^2 ≤ (r0 a-delta/2)^2 := by
    have := hrpos a
    have := (hr a).2
    nlinarith
  intro i
  exact (hb a (r a) hr2 m i).mono_const
    (Finset.single_le_sum (fun b _ => hB b m) (Finset.mem_univ a))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
