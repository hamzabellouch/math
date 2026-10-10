import OAI.Geometry.NodalSets.Charts.CorrugationRotatingFrame
import OAI.Geometry.NodalSets.Charts.MetricNormalizationBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma corrugationFastVector_center (amp : ℝ) (e : Coord ≃L[ℝ] Coord) (z : ℝ × ℝ)
    (hr : corrugationCellRadius z = 0) : corrugationFastVector amp e z = 0 := by
  have hh := (corrugationCellRadius_properties z).2
  rw [hr] at hh
  have h1 : (corrugationCellPoint z).1 = 0 := by nlinarith [sq_nonneg (corrugationCellPoint z).2]
  have h2 : (corrugationCellPoint z).2 = 0 := by nlinarith [sq_nonneg (corrugationCellPoint z).1]
  simp [corrugationFastVector,(corrugationPeriodicWell_global_jets amp z).1,
    corrugationDiskWell_fderiv,h1,h2]

lemma corrugationLeadingVector_global_length (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (amp t : ℝ) (z : ℝ × ℝ) :
    g (corrugationLeadingVector amp t e z) (corrugationLeadingVector amp t e z) =
      1+(t*corrugationSlope amp (1/4) (corrugationCellRadius z))^2 := by
  by_cases hr : corrugationCellRadius z = 0
  · simp [corrugationLeadingVector,corrugationFastVector_center amp e z hr,hr,corrugationSlope,he]
  · exact corrugationLeadingVector_metric_length g e he amp t z hr

lemma corrugationLeadingVector_length_ge_one (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (amp t : ℝ) (z : ℝ × ℝ) :
    1 ≤ g (corrugationLeadingVector amp t e z) (corrugationLeadingVector amp t e z) := by
  rw [corrugationLeadingVector_global_length g e he]
  linarith [sq_nonneg (t*corrugationSlope amp (1/4) (corrugationCellRadius z))]

lemma metricNormalize_positive_smul (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (v : Coord) {s : ℝ} (hs : 0 < s) :
    metricNormalize g (s • v) = metricNormalize g v := by
  unfold metricNormalize
  simp only [map_smul,smul_apply,smul_eq_mul]
  have hid : s*(s*g v v) = s^2*(g v v) := by ring
  rw [hid,Real.sqrt_mul (sq_nonneg s),Real.sqrt_sq_eq_abs,abs_of_pos hs,
    mul_inv_rev,smul_smul]
  congr 1
  field_simp

lemma inverse_scaled_vector_error (p q : Coord) {s E : ℝ} (hs : 0 < s)
    (h : ‖p-s • q‖ ≤ s*E) : ‖s⁻¹ • p-q‖ ≤ E := by
  have hid : s⁻¹ • p-q = s⁻¹ • (p-s • q) := by
    rw [smul_sub,smul_smul,inv_mul_cancel₀ hs.ne',one_smul]
  rw [hid,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
  calc
    _ ≤ s⁻¹*(s*E) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hs.le)
    _ = E := by field_simp

end
end Yau.Geometry

end OAI
