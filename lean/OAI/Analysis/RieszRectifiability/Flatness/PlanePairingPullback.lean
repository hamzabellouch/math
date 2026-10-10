import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.PlaneHeightDistribution
import OAI.Analysis.RieszRectifiability.Kernel.HeightPairingRegions

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem affine_plane_pair_integral {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (A B : Set (Ambient d))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (F : Ambient d × Ambient d → ℝ) :
    (∫ q, F q ∂((coordinatePlaneMeasure (affinePlaneSection a L)).restrict A).prod
      ((coordinatePlaneMeasure (affinePlaneSection a L)).restrict B)) =
    ∫ q : Ambient n × Ambient n, F (a + L q.1, a + L q.2)
      ∂(volume.restrict ((fun u : Ambient n => a + L u) ⁻¹' A)).prod
        (volume.restrict ((fun u : Ambient n => a + L u) ⁻¹' B)) := by
  have he : Isometry (fun u : Ambient n => a + L u) := by
    apply Isometry.of_dist_eq
    intro u v
    simp only [dist_add_left, L.dist_map]
  rw [coordinatePlaneMeasure_affine_eq_map,
    Measure.restrict_map he.continuous.measurable hA,
    Measure.restrict_map he.continuous.measurable hB,
    Measure.map_prod_map _ _ he.continuous.measurable he.continuous.measurable]
  exact (he.isClosedEmbedding.measurableEmbedding.prodMap
    he.isClosedEmbedding.measurableEmbedding).integral_map F

theorem affine_plane_pair_integrable_iff {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (A B : Set (Ambient d))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (F : Ambient d × Ambient d → ℝ) :
    Integrable F (((coordinatePlaneMeasure (affinePlaneSection a L)).restrict A).prod
      ((coordinatePlaneMeasure (affinePlaneSection a L)).restrict B)) ↔
    Integrable (fun q : Ambient n × Ambient n => F (a + L q.1, a + L q.2))
      ((volume.restrict ((fun u : Ambient n => a + L u) ⁻¹' A)).prod
        (volume.restrict ((fun u : Ambient n => a + L u) ⁻¹' B))) := by
  have he : Isometry (fun u : Ambient n => a + L u) := by
    apply Isometry.of_dist_eq
    intro u v
    simp only [dist_add_left, L.dist_map]
  rw [coordinatePlaneMeasure_affine_eq_map,
    Measure.restrict_map he.continuous.measurable hA,
    Measure.restrict_map he.continuous.measurable hB,
    Measure.map_prod_map _ _ he.continuous.measurable he.continuous.measurable]
  exact (he.isClosedEmbedding.measurableEmbedding.prodMap
    he.isClosedEmbedding.measurableEmbedding).integrable_map_iff

theorem fractionalBilinear_affine_pullback {n d : ℕ} (m : ℕ) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f φ : Ambient d → ℝ) (u v : Ambient n) :
    fractionalBilinear m f φ (a + L u) (a + L v) =
      fractionalBilinear m (fun x => f (a + L x)) (fun x => φ (a + L x)) u v := by
  simp only [fractionalBilinear, dist_add_left, L.dist_map]

theorem renormalizedNormalIntegrand_affine_pullback {n d : ℕ} (m : ℕ) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f φ : Ambient d → ℝ) (q : Ambient n × Ambient n) :
    renormalizedNormalIntegrand m f φ a (a + L q.1, a + L q.2) =
      renormalizedNormalIntegrand m (fun x => f (a + L x)) (fun x => φ (a + L x)) 0 q := by
  have ha : dist a (a + L q.2) = dist (0 : Ambient n) q.2 := by
    simpa only [map_zero, add_zero] using!
      (show dist (a + L 0) (a + L q.2) = dist (0 : Ambient n) q.2 from by
        rw [dist_add_left, L.dist_map])
  simp only [renormalizedNormalIntegrand, inverseDistancePow, dist_add_left, L.dist_map, ha]

theorem heightPairingOn_affine_pullback {n d : ℕ} (m : ℕ) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f φ : Ambient d → ℝ) (R : ℝ) :
    heightPairingOn m (coordinatePlaneMeasure (affinePlaneSection a L)) a (ball a R) f φ =
      heightPairingOn m volume (0 : Ambient n) (ball 0 R)
        (fun u => f (a + L u)) (fun u => φ (a + L u)) := by
  have hpre : (fun u : Ambient n => a + L u) ⁻¹' ball a R = ball 0 R := by
    ext u
    simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero, L.norm_map]
  unfold heightPairingOn
  rw [affine_plane_pair_integral a L (ball a R) (ball a R) measurableSet_ball measurableSet_ball,
    affine_plane_pair_integral a L (ball a R) (ball a R)ᶜ measurableSet_ball measurableSet_ball.compl]
  simp only [preimage_compl, hpre, fractionalBilinear_affine_pullback,
    renormalizedNormalIntegrand_affine_pullback]

end

end RieszRectifiability

end OAI
