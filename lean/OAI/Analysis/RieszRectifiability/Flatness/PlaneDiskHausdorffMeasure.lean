import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal Pointwise

def planeUnitHausdorffMeasure (n : ℕ) : ℝ≥0∞ :=
  (μH[(n : ℝ)] : Measure (Ambient n)) (closedBall 0 1)

theorem planeUnitHausdorffMeasure_lt_top (n : ℕ) :
    planeUnitHausdorffMeasure n < ⊤ := by
  have h := (isCompact_closedBall (0 : Ambient n) 1).measure_lt_top
    (μ := (μH[(Module.finrank ℝ (Ambient n) : ℝ)] : Measure (Ambient n)))
  simpa only [finrank_euclideanSpace_fin, planeUnitHausdorffMeasure] using! h

theorem plane_closedBall_hausdorffMeasure {n d : ℕ}
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (a : P) (r : ℝ) (hr : 0 < r) :
    (μH[(n : ℝ)] : Measure P) (closedBall a r) =
      (ENNReal.ofReal r) ^ n * planeUnitHausdorffMeasure n := by
  let b : OrthonormalBasis (Fin n) ℝ P :=
    (stdOrthonormalBasis ℝ P).reindex (finCongr hdim)
  let E : Ambient n ≃ₗᵢ[ℝ] P := b.repr.symm
  have hd : 0 ≤ (n : ℝ) := by positivity
  have hE : (μH[(n : ℝ)] : Measure P) (closedBall 0 r) =
      (μH[(n : ℝ)] : Measure (Ambient n)) (closedBall 0 r) := by
    have h := E.isometry.hausdorffMeasure_image (Or.inl hd) (closedBall 0 r)
    have himage : E '' closedBall 0 r = closedBall 0 r := by
      have h' := E.toIsometryEquiv.image_closedBall 0 r
      change E '' closedBall 0 r = closedBall (E 0) r at h'
      simpa only [map_zero] using! h'
    rw [himage] at h
    exact h
  have htranslate : (μH[(n : ℝ)] : Measure P) (closedBall a r) =
      (μH[(n : ℝ)] : Measure P) (closedBall 0 r) := by
    have h := (IsometryEquiv.addRight a).isometry.hausdorffMeasure_image
      (Or.inl hd) (closedBall 0 r)
    rw [(IsometryEquiv.addRight a).image_closedBall] at h
    change (μH[(n : ℝ)] : Measure P) (closedBall (0 + a) r) = _ at h
    simpa only [zero_add] using! h
  have hscale := Measure.hausdorffMeasure_smul₀ (𝕜 := ℝ) hd hr.ne'
    (closedBall (0 : Ambient n) 1)
  have hnorm : (‖r‖₊ : ℝ≥0∞) = ENNReal.ofReal r := by
    rw [← Real.toNNReal_eq_nnnorm_of_nonneg hr.le]
    rfl
  rw [htranslate, hE]
  simpa only [smul_closedBall' hr.ne', smul_zero, Real.norm_of_nonneg hr.le,
    mul_one, NNReal.rpow_natCast, ENNReal.smul_def, smul_eq_mul,
    ENNReal.coe_pow, hnorm, planeUnitHausdorffMeasure] using! hscale

theorem plane_closedBall_subtype_hausdorffMeasure {n d : ℕ}
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (a : P) (r : ℝ) (hr : 0 < r) :
    (μH[(n : ℝ)] : Measure (closedBall a r)) Set.univ =
      (ENNReal.ofReal r) ^ n * planeUnitHausdorffMeasure n := by
  have h := (isometry_subtype_coe (s := closedBall a r)).hausdorffMeasure_image
    (Or.inl (show 0 ≤ (n : ℝ) by positivity)) Set.univ
  have heq : (μH[(n : ℝ)] : Measure (closedBall a r)) Set.univ =
      (μH[(n : ℝ)] : Measure P) (closedBall a r) := by
    simpa only [Set.image_univ, Subtype.range_coe] using! h.symm
  rw [heq, plane_closedBall_hausdorffMeasure P hdim a r hr]

theorem plane_disk_lipschitz_range_hausdorffMeasure_le {n d e : ℕ}
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (a : P) (r : ℝ) (hr : 0 < r) (K : ℝ≥0)
    (g : closedBall a r → Ambient e) (hg : LipschitzWith K g) :
    (μH[(n : ℝ)] : Measure (Ambient e)) (Set.range g) ≤
      (K : ℝ≥0∞) ^ n * ((ENNReal.ofReal r) ^ n * planeUnitHausdorffMeasure n) := by
  have h := hg.hausdorffMeasure_image_le (show 0 ≤ (n : ℝ) by positivity) Set.univ
  simpa only [Set.image_univ, ENNReal.rpow_natCast,
    plane_closedBall_subtype_hausdorffMeasure P hdim a r hr] using! h

end

end RieszRectifiability

end OAI
