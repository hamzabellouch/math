import OAI.Geometry.CylinderCovering.Ruled.CellArea

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ProductCells

@[simp] lemma coordinateEquiv_apply_zero (p : Plane) : coordinateEquiv p 0 = p.1 := rfl
@[simp] lemma coordinateEquiv_apply_one (p : Plane) : coordinateEquiv p 1 = p.2 := rfl
@[simp] lemma coordinateEquiv_symm_apply (x : Fin 2 → ℝ) :
    coordinateEquiv.symm x = (x 0,x 1) := rfl

lemma coordinateEquiv_measurePreserving : MeasurePreserving coordinateEquiv volume volume := by
  exact (volume_preserving_finTwoArrow ℝ).symm _

lemma coordinate_image_volume (S : Set Plane) :
    volume (coordinateEquiv '' S) = volume S := by
  rw [← coordinateEquiv_measurePreserving.map_eq]
  have hemb : MeasurableEmbedding coordinateEquiv :=
    coordinateEquiv.toHomeomorph.measurableEmbedding
  rw [hemb.map_apply]
  rw [preimage_image_eq S coordinateEquiv.injective]

lemma coordinate_image_area (S : Set Plane) :
    volume.real (coordinateEquiv '' S) = volume.real S := by
  simp only [Measure.real_def,coordinate_image_volume]

lemma mem_coordinateParameterCell {tau : ℝ} {x : Fin 2 → ℝ} :
    x ∈ coordinateParameterCell tau ↔ |x 0| ≤ 1 ∧ |x 1| ≤ 1 ∧ |x 0*x 1| ≤ tau := by
  change x ∈ coordinateEquiv '' parameterCell tau ↔ _
  rw [coordinateEquiv.image_eq_preimage_symm]
  rfl

lemma mem_coordinateInterceptCell {tau gamma : ℝ} {x : Fin 2 → ℝ} :
    x ∈ coordinateInterceptCell tau gamma ↔
      |x 0| < 3 ∧ |x 1| < 3 ∧ |x 0*x 1| < (1+gamma)*tau := by
  change x ∈ coordinateEquiv '' interceptCell tau gamma ↔ _
  rw [coordinateEquiv.image_eq_preimage_symm]
  rfl

lemma coordinateParameterCell_isCompact (tau : ℝ) : IsCompact (coordinateParameterCell tau) :=
  (closedCell_isCompact 1 tau).image coordinateEquiv.continuous

lemma coordinateInterceptCell_isOpen (tau gamma : ℝ) : IsOpen (coordinateInterceptCell tau gamma) :=
  coordinateEquiv.toHomeomorph.isOpenMap _ (openCell_isOpen 3 ((1+gamma)*tau))

lemma coordinateInterceptCell_isBounded (tau gamma : ℝ) :
    Bornology.IsBounded (coordinateInterceptCell tau gamma) :=
  (openCell_isBounded 3 ((1+gamma)*tau)).image coordinateEquiv.toContinuousLinearMap

lemma coordinate_parameter_area {tau : ℝ} (htau : 0 < tau) (htau1 : tau < 1) :
    volume.real (coordinateParameterCell tau) = 4*tau*(1+Real.log (1/tau)) := by
  rw [coordinateParameterCell,coordinate_image_area]
  simpa [parameterCell] using area_closedCell (A:=1) (by norm_num) htau (by nlinarith)

lemma coordinate_intercept_area {tau gamma : ℝ}
    (htau : 0 < tau) (hg : 0 ≤ gamma) (hpad : (1+gamma)*tau < 1) :
    volume.real (coordinateInterceptCell tau gamma) =
      4*((1+gamma)*tau)*(1+Real.log (9/((1+gamma)*tau))) := by
  rw [coordinateInterceptCell,coordinate_image_area]
  have hB : 0 < (1+gamma)*tau := mul_pos (by linarith) htau
  have h := area_openCell (A:=3) (by norm_num) hB (by nlinarith)
  norm_num at h
  exact h

lemma coordinate_area_ratio {tau gamma : ℝ}
    (htau : 0 < tau) (htau1 : tau < 1) (hg : 0 ≤ gamma)
    (hpad : (1+gamma)*tau < 1) :
    volume.real (coordinateInterceptCell tau gamma) /
      volume.real (coordinateParameterCell tau) = areaRatio tau gamma := by
  simp only [coordinateInterceptCell,coordinateParameterCell,coordinate_image_area]
  exact geometric_area_ratio htau htau1 hg hpad

lemma expanded_coordinateParameterCell_mem_intercept {z tau gamma eps : ℝ}
    {s e : Fin 2 → ℝ} (hz : |z| ≤ 1) (hs : s ∈ coordinateParameterCell tau)
    (he₁ : |e 0| ≤ eps) (he₂ : |e 1| ≤ eps)
    (heps : eps < 1/2) (hgap : eps < gamma*tau/5) :
    (![(1+z)*s 0+e 0, (1-z)*s 1+e 1] : Fin 2 → ℝ) ∈ coordinateInterceptCell tau gamma := by
  rw [mem_coordinateParameterCell] at hs
  rw [mem_coordinateInterceptCell]
  exact expanded_parameterCell_mem_intercept (s:=(s 0,s 1)) (e:=(e 0,e 1))
    hz hs he₁ he₂ heps hgap

end ProductCells

end

end OAI
