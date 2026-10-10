import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.PlanePairingPullback

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem affine_plane_ball_preimage {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (R : ℝ) :
    (fun u : Ambient n => a + L u) ⁻¹' ball a R = ball 0 R := by
  ext u
  simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero, L.norm_map]

theorem affine_plane_exterior_preimage {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (R : ℝ) :
    (fun u : Ambient n => a + L u) ⁻¹' closedExterior a R = closedExterior 0 R := by
  rw [closedExterior_eq_compl_ball, preimage_compl, affine_plane_ball_preimage,
    ← closedExterior_eq_compl_ball]

theorem affine_plane_integrableOn_iff {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (F : Ambient d → ℝ) :
    IntegrableOn F s (coordinatePlaneMeasure (affinePlaneSection a L)) ↔
      IntegrableOn (fun u : Ambient n => F (a + L u))
        ((fun u : Ambient n => a + L u) ⁻¹' s) volume := by
  have he : Isometry (fun u : Ambient n => a + L u) := by
    apply Isometry.of_dist_eq
    intro u v
    simp only [dist_add_left, L.dist_map]
  rw [IntegrableOn, coordinatePlaneMeasure_affine_eq_map,
    Measure.restrict_map he.continuous.measurable hs]
  exact he.isClosedEmbedding.measurableEmbedding.integrable_map_iff

theorem height_local_integrable_affine_pullback {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient d → ℝ) (R : ℝ)
    (hi : IntegrableOn f (ball a R) (coordinatePlaneMeasure (affinePlaneSection a L))) :
    IntegrableOn (fun u : Ambient n => f (a + L u)) (ball 0 R) volume := by
  simpa only [affine_plane_ball_preimage] using!
    (affine_plane_integrableOn_iff a L (ball a R) measurableSet_ball f).mp hi

theorem height_tail_integrable_affine_pullback {n d : ℕ} (q : ℕ) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient d → ℝ) (R : ℝ)
    (hi : IntegrableOn (fun x => |f x| * inverseDistancePow q a x) (closedExterior a R)
      (coordinatePlaneMeasure (affinePlaneSection a L))) :
    IntegrableOn (fun u : Ambient n => |f (a + L u)| * inverseDistancePow q 0 u)
      (closedExterior 0 R) volume := by
  have h := (affine_plane_integrableOn_iff a L (closedExterior a R)
    (closedExterior_measurable a R) (fun x => |f x| * inverseDistancePow q a x)).mp hi
  have hd (u : Ambient n) : dist a (a + L u) = dist (0 : Ambient n) u := by
    simpa only [map_zero, add_zero] using!
      (show dist (a + L 0) (a + L u) = dist (0 : Ambient n) u from by
        rw [dist_add_left, L.dist_map])
  simpa only [affine_plane_exterior_preimage, inverseDistancePow, hd] using! h

theorem height_energy_integrable_affine_pullback {n d : ℕ} (m : ℕ) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient d → ℝ) (R : ℝ)
    (hi : Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m f q.1 q.2)
      (((coordinatePlaneMeasure (affinePlaneSection a L)).restrict (ball a R)).prod
        ((coordinatePlaneMeasure (affinePlaneSection a L)).restrict (ball a R)))) :
    Integrable (fun q : Ambient n × Ambient n =>
      fractionalPairEnergy m (fun u => f (a + L u)) q.1 q.2)
      ((volume.restrict (ball (0 : Ambient n) R)).prod (volume.restrict (ball 0 R))) := by
  have h := (affine_plane_pair_integrable_iff a L (ball a R) (ball a R)
    measurableSet_ball measurableSet_ball
    (fun q => fractionalPairEnergy m f q.1 q.2)).mp hi
  simpa only [affine_plane_ball_preimage, fractionalPairEnergy, dist_add_left, L.dist_map] using! h

end

end RieszRectifiability

end OAI
