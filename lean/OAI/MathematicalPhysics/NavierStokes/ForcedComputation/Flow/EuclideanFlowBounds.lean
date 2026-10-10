import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.EuclideanConjugacy

namespace OAI

/-! The Euclidean quantitative clause of the planar-processor theorem, with
one computed integer bounding the spatial derivatives. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set
open scoped ContDiff

theorem euclideanFlowBound_one_le (H : FieldExpr) : 1 ≤ euclideanFlowBound H := by
  have hp := planarVariationCoefficient_pos H
  unfold euclideanFlowBound euclideanVariationCoefficient
  omega

theorem euclidean_field_bounds {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) (s : ℝ) (x : EuclideanPlane) :
    ‖fderiv ℝ (euclideanMap (planarSlice H s)) x‖ ≤ (euclideanFlowBound H : ℝ) ∧
    ‖fderiv ℝ (fderiv ℝ (euclideanMap (planarSlice H s))) x‖ ≤
      (euclideanFlowBound H : ℝ) := by
  have hb := planar_euclidean_derivative_bounds hH hT s x
  have hle : (euclideanVariationCoefficient H : ℝ) ≤ (euclideanFlowBound H : ℝ) := by
    unfold euclideanFlowBound
    push_cast
    nlinarith [show (0 : ℝ) ≤ euclideanVariationCoefficient H from Nat.cast_nonneg _]
  exact ⟨hb.1.trans hle, hb.2.trans hle⟩

theorem planar_euclidean_flow_estimates {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) {Ω : ℝ → ℝ → Plane → Plane}
    (hv : PlanarVariations (planarSlice H) Ω) :
    1 ≤ euclideanFlowBound H ∧
    (∀ s x, ‖fderiv ℝ (euclideanMap (planarSlice H s)) x‖ ≤ (euclideanFlowBound H : ℝ) ∧
      ‖fderiv ℝ (fderiv ℝ (euclideanMap (planarSlice H s))) x‖ ≤ (euclideanFlowBound H : ℝ)) ∧
    ∀ a t, 0 ≤ t →
      (∀ x, (‖fderiv ℝ (euclideanMap (Ω a t)) x‖ ≤ Real.exp ((euclideanFlowBound H : ℝ) * t) ∧
        ‖fderiv ℝ (fderiv ℝ (euclideanMap (Ω a t))) x‖ ≤
          Real.exp (2 * (euclideanFlowBound H : ℝ) * t) -
            Real.exp ((euclideanFlowBound H : ℝ) * t)) ∧
        (‖fderiv ℝ (euclideanMap (Ω (a + t) (-t))) x‖ ≤ Real.exp ((euclideanFlowBound H : ℝ) * t) ∧
        ‖fderiv ℝ (fderiv ℝ (euclideanMap (Ω (a + t) (-t)))) x‖ ≤
          Real.exp (2 * (euclideanFlowBound H : ℝ) * t) -
            Real.exp ((euclideanFlowBound H : ℝ) * t))) ∧
      (∀ x y, dist (euclideanMap (Ω a t) x) (euclideanMap (Ω a t) y) ≤
        Real.exp ((euclideanFlowBound H : ℝ) * t) * dist x y) := by
  have he := hv.euclidean (fun s => planarSlice_smooth hH s)
  refine ⟨euclideanFlowBound_one_le H, euclidean_field_bounds hH hT, ?_⟩
  intro a t ht
  constructor
  · intro x
    exact ⟨euclidean_quantitative_variations hH hT he a x ht,
      euclidean_inverse_estimates hH hT he a x ht⟩
  · intro x y
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (s := (univ : Set EuclideanPlane))
      (fun z _ => (he.smooth a t).differentiable (by simp) z)
      (fun z _ => (euclidean_quantitative_variations hH hT he a z ht).1)
      (convex_univ : Convex ℝ (univ : Set EuclideanPlane)) (mem_univ y) (mem_univ x)
    simpa only [dist_eq_norm] using h

end ForcedComputation

end

end OAI
