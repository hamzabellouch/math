import OAI.Geometry.SurfaceImmersion.Atlas.ShrinkingWeightBounds
import OAI.Geometry.SurfaceImmersion.Geometry.VectorPlaneRestore

namespace OAI

/-! Fixed atlas bounds for an entire compact box of actual smaller-radius weights. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
open JetPolynomial (planeCoordinateIsometry weightedBound_comp_isometry)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- All finite derivative bounds are fixed before selecting the new radius. -/
theorem shrinking_weight_atlas_bounds (i : A.centers) {r0 R : ℝ}
    (hreg0 : circularCoordinateRegion (i : M) r0 ⊆ (coordinateChart (i : M)).target)
    (hR : R^2 < r0^2) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ ∀ r : ℝ, r^2 ≤ R^2 →
      ∀ m, A.WeightedBound 1 m (C m) (shrinkingCircularWeight (i : M) (A.weight i) r0 r) := by
  classical
  obtain ⟨a,ha,heq,B,hB,hbound⟩ := shrinkingWeight_coordinate_bounds
    (i : M) (A.weight i) (A.weight_smooth i) hreg0 hR
  let f : ℝ → SmallModes.Base → ℝ := fun r x =>
    a x * circularFlatBump (coordinateChart (i : M) (i : M)) r x
  have hf (r : ℝ) : ContDiff ℝ ∞ (f r) :=
    ha.mul (circularFlatBump_smooth _ r)
  have hrestore (r : ℝ) (hr : r^2 ≤ R^2) :
      shrinkingCircularWeight (i : M) (A.weight i) r0 r =
        restore (i : M) (A.outer i) (f r ∘ planeCoordinateIsometry) := by
    funext x
    by_cases hx : x ∈ (chart (i : M)).source
    · have hx' : x ∈ (coordinateChart (i : M)).source := by
        simpa only [coordinateChart_source,chart_source] using hx
      have hval := heq r hr (coordinateChart (i : M) x)
        ((coordinateChart (i : M)).map_source hx')
      rw [(coordinateChart (i : M)).left_inv hx'] at hval
      have hval' : shrinkingCircularWeight (i : M) (A.weight i) r0 r x =
          f r (planeCoordinateIsometry (chart (i : M) x)) := hval
      rw [restore,indicator_of_mem hx,Function.comp_apply,← hval']
      by_cases hz : A.weight i x = 0
      · simp only [shrinkingCircularWeight,hz,zero_mul,smul_zero]
      · rw [A.outer_one i x (subset_tsupport _ hz),one_smul]
    · have hw : A.weight i x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hh => hx (A.weight_support i hh))
      simp only [restore,indicator_of_notMem hx,shrinkingCircularWeight,hw,zero_mul]
  choose D hD hlocal using fun m j => A.pair_weighted_bound (V := ℝ) j i m
  refine ⟨fun m => (∑ j : A.centers, D m j)*B m,?_,?_⟩
  · intro m
    exact mul_nonneg (Finset.sum_nonneg (fun j _ => hD m j)) (hB m)
  · intro r hr m j
    rw [hrestore r hr]
    exact (hlocal m j (f r ∘ planeCoordinateIsometry) 1 (B m) zero_lt_one le_rfl (hB m) ( (hf r).comp planeCoordinateIsometry.contDiff)
      (weightedBound_comp_isometry planeCoordinateIsometry (hf r) (hbound r hr m))).mono_const (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => hD m k) (Finset.mem_univ j)) (hB m))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
