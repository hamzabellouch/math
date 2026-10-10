import OAI.MeasureTheory.Falconer.Slicing.HyperplaneSliceEnergy
import OAI.MeasureTheory.Falconer.Radial.HyperplaneEnergy
import OAI.MeasureTheory.Falconer.Fourier.ConeIntegration
import Mathlib.Analysis.Calculus.ContDiff.WithLp

namespace OAI

/-! Volume coordinates on a fixed normal's orthogonal hyperplane and fibers. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def hyperplaneProjection {n : ℕ} (w : Sphere (n+1))
    (x : Space (n+1)) : Space n :=
  euclideanTail (northRotation w x)

noncomputable def hyperplaneFrame {n : ℕ} (w : Sphere (n+1))
    (p : Space n × ℝ) : Space (n+1) :=
  (northRotation w).symm (coordinateJoin p.1 p.2)

@[fun_prop] theorem contDiff_hyperplaneProjection {n : ℕ} (w : Sphere (n+1)) :
    ContDiff ℝ (⊤ : ℕ∞) (hyperplaneProjection w) := by
  unfold hyperplaneProjection euclideanTail
  apply (contDiff_piLp 2).mpr
  intro i
  exact (contDiff_piLp_apply 2 (i := i.succ)).comp (northRotation w).contDiff

@[fun_prop] theorem contDiff_hyperplaneFrame {n : ℕ} (w : Sphere (n+1)) :
    ContDiff ℝ (⊤ : ℕ∞) (hyperplaneFrame w) := by
  apply (northRotation w).symm.contDiff.comp
  apply (contDiff_piLp 2).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp only [coordinateJoin_eq]
  · exact contDiff_snd
  · exact (contDiff_piLp_apply 2 (i := j)).comp contDiff_fst

theorem hyperplaneProjection_frame {n : ℕ} (w : Sphere (n+1)) (y : Space n) (t : ℝ) :
    hyperplaneProjection w (hyperplaneFrame w (y,t)) = y := by
  simp only [hyperplaneProjection, hyperplaneFrame, LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro i
  simp [euclideanTail, coordinateJoin_eq]

theorem hyperplaneFrame_inner {n : ℕ} (w : Sphere (n+1)) (p : Space n × ℝ) :
    inner ℝ (hyperplaneFrame w p) (w : Space (n+1)) = p.2 := by
  rw [hyperplaneFrame, ← (northRotation w).inner_map_map,
    LinearIsometryEquiv.apply_symm_apply, northRotation_apply,
    gnomonicChart_zero_coe, inner_northLift_zero]
  simp [coordinateJoin_eq]

theorem hyperplaneFrame_reconstruct {n : ℕ} (w : Sphere (n+1)) (x : Space (n+1)) :
    hyperplaneFrame w (hyperplaneProjection w x, inner ℝ x (w : Space (n+1))) = x := by
  apply (northRotation w).injective
  simp only [hyperplaneFrame, LinearIsometryEquiv.apply_symm_apply]
  have hi : inner ℝ x (w : Space (n+1)) = (northRotation w x) 0 := by
    rw [← (northRotation w).inner_map_map, northRotation_apply,
      gnomonicChart_zero_coe, inner_northLift_zero]
  rw [hi]
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [coordinateJoin_eq, hyperplaneProjection, euclideanTail]

theorem hyperplaneFrame_volume {n : ℕ} (w : Sphere (n+1)) :
    MeasurePreserving (hyperplaneFrame w) (volume.prod volume) volume :=
  (northRotation w).symm.measurePreserving.comp (coordinateEquiv_measurePreserving n).symm

theorem hyperplaneFrame_add {n : ℕ} (w : Sphere (n+1)) (p q : Space n × ℝ) :
    hyperplaneFrame w (p+q) = hyperplaneFrame w p + hyperplaneFrame w q := by
  unfold hyperplaneFrame
  rw [← map_add]
  congr 1
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [coordinateJoin_eq]

theorem hyperplaneFrame_smul {n : ℕ} (w : Sphere (n+1)) (r : ℝ) (p : Space n × ℝ) :
    hyperplaneFrame w (r • p) = r • hyperplaneFrame w p := by
  unfold hyperplaneFrame
  rw [← map_smul]
  congr 1
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [coordinateJoin_eq]

theorem hyperplaneFrame_axis {n : ℕ} (w : Sphere (n+1)) (t : ℝ) :
    hyperplaneFrame w (0,t) = t • (w : Space (n+1)) := by
  apply (northRotation w).injective
  simp only [hyperplaneFrame, LinearIsometryEquiv.apply_symm_apply, map_smul,
    northRotation_apply, gnomonicChart_zero_coe]
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [coordinateJoin_eq, northLift]

theorem hyperplaneFrame_fiber {n : ℕ} (w : Sphere (n+1)) (y : Space n) (t : ℝ) :
    hyperplaneFrame w (y,t) = hyperplaneSliceEmbedding w y + t • (w : Space (n+1)) := by
  rw [show (y,t) = (y,0) + (0,t) by simp, hyperplaneFrame_add, hyperplaneFrame_axis]
  rfl

theorem hyperplaneProjection_sub {n : ℕ} (w : Sphere (n+1)) (x y : Space (n+1)) :
    hyperplaneProjection w (x-y) = hyperplaneProjection w x - hyperplaneProjection w y := by
  apply PiLp.ext
  intro i
  simp [hyperplaneProjection, euclideanTail, map_sub]

theorem hyperplaneSliceEmbedding_projection {n : ℕ} (w : Sphere (n+1)) (x : Space (n+1)) :
    hyperplaneSliceEmbedding w (hyperplaneProjection w x) = perpendicularPart (w : Space (n+1)) x := by
  have h := hyperplaneFrame_reconstruct w x
  rw [hyperplaneFrame_fiber] at h
  unfold perpendicularPart
  rw [real_inner_comm]
  exact eq_sub_iff_add_eq.mpr h

theorem hyperplaneProjection_dist {n : ℕ} (w : Sphere (n+1)) (x y : Space (n+1)) :
    dist (hyperplaneProjection w x) (hyperplaneProjection w y) =
      dist (perpendicularPart (w : Space (n+1)) x) (perpendicularPart (w : Space (n+1)) y) := by
  rw [dist_eq_norm, dist_eq_norm, ← hyperplaneProjection_sub,
    ← hyperplaneSliceEmbedding_norm w, hyperplaneSliceEmbedding_projection,
    perpendicularPart_sub]

noncomputable def hyperplaneCoordinateMeasure {n : ℕ} (μ : Measure (Space (n+1)))
    (w : Sphere (n+1)) : Measure (Space n) := μ.map (hyperplaneProjection w)

theorem hyperplaneCoordinateMeasure_energy {n : ℕ} (μ : Measure (Space (n+1)))
    [IsFiniteMeasure μ] (w : Sphere (n+1)) (t : ℝ) :
    PlanarFalconer.rieszEnergyOn (hyperplaneCoordinateMeasure μ w) t =
      PlanarFalconer.rieszEnergyOn (hyperplaneProjectedMeasure μ w) t := by
  have hm := (contDiff_hyperplaneProjection w).continuous.measurable
  rw [PlanarFalconer.rieszEnergyOn, hyperplaneCoordinateMeasure,
    Measure.map_prod_map μ μ hm hm, lintegral_map (by fun_prop) (hm.prodMap hm),
    hyperplane_projected_energy_formula]
  apply lintegral_congr
  intro z
  simp only [Prod.map, edist_dist]
  simpa only [dist_eq_norm, perpendicularPart_sub] using
    congrArg (fun r : ℝ => (ENNReal.ofReal r)^(-t)) (hyperplaneProjection_dist w z.1 z.2)

end Falconer

end OAI
