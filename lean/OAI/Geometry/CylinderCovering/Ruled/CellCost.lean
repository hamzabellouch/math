import OAI.Geometry.CylinderCovering.Ruled.CellCoordinates
import OAI.Geometry.CylinderCovering.Ruled.Projection

namespace OAI

noncomputable section
open Set MeasureTheory
namespace ProductCells

lemma translated_frame_area (M : RuledApproximation.Coordinates ≃L[ℝ] RuledApproximation.Plane)
    (p : RuledApproximation.Plane) {S : Set RuledApproximation.Coordinates}
    (hS : MeasurableSet S) :
    volume.real ((fun x => p + M x) '' S) =
      RuledApproximation.frameJacobian M * volume.real S := by
  have himage : (fun x => p + M x) '' S = (fun y => p+y) '' (M '' S) := by
    rw [← image_comp]
    rfl
  rw [himage]
  have htrans : volume.real ((fun y => p+y) '' (M '' S)) = volume.real (M '' S) := by
    simp only [Measure.real_def,image_add_left,measure_preimage_add]
  rw [htrans,RuledApproximation.frame_volume_image M hS]

lemma coordinate_parameter_area_pos {tau : ℝ} (htau : 0 < tau) (htau1 : tau < 1) :
    0 < volume.real (coordinateParameterCell tau) := by
  rw [coordinate_parameter_area htau htau1]
  have hlog : 0 ≤ Real.log (1/tau) := Real.log_nonneg ((le_div_iff₀ htau).mpr (by linarith))
  positivity

lemma framed_intercept_area (M : RuledApproximation.Coordinates ≃L[ℝ] RuledApproximation.Plane)
    (p : RuledApproximation.Plane) {tau gamma : ℝ}
    (htau : 0 < tau) (htau1 : tau < 1) (hg : 0 ≤ gamma)
    (hpad : (1+gamma)*tau < 1) :
    volume.real ((fun x => p+M x) '' coordinateInterceptCell tau gamma) =
      areaRatio tau gamma * volume.real ((fun x => p+M x) '' coordinateParameterCell tau) := by
  have hratio := coordinate_area_ratio htau htau1 hg hpad
  have hQ := coordinate_parameter_area_pos htau htau1
  have harea := (div_eq_iff (ne_of_gt hQ)).mp hratio
  rw [translated_frame_area M p (coordinateInterceptCell_isOpen tau gamma).measurableSet,
    translated_frame_area M p (coordinateParameterCell_isCompact tau).measurableSet,harea]
  ring

lemma framed_parameter_isCompact
    (M : RuledApproximation.Coordinates ≃L[ℝ] RuledApproximation.Plane)
    (p : RuledApproximation.Plane) (tau : ℝ) :
    IsCompact ((fun x => p+M x) '' coordinateParameterCell tau) :=
  (coordinateParameterCell_isCompact tau).image (continuous_const.add M.continuous)

lemma framed_intercept_isOpen
    (M : RuledApproximation.Coordinates ≃L[ℝ] RuledApproximation.Plane)
    (p : RuledApproximation.Plane) (tau gamma : ℝ) :
    IsOpen ((fun x => p+M x) '' coordinateInterceptCell tau gamma) := by
  have heq : (fun x => p+M x) '' coordinateInterceptCell tau gamma =
      (fun y => p+y) '' (M '' coordinateInterceptCell tau gamma) := by
    rw [← image_comp]
    rfl
  rw [heq]
  exact (Homeomorph.addLeft p).isOpenMap _
    (M.toHomeomorph.isOpenMap _ (coordinateInterceptCell_isOpen tau gamma))

lemma framed_intercept_isBounded
    (M : RuledApproximation.Coordinates ≃L[ℝ] RuledApproximation.Plane)
    (p : RuledApproximation.Plane) (tau gamma : ℝ) :
    Bornology.IsBounded ((fun x => p+M x) '' coordinateInterceptCell tau gamma) := by
  unfold coordinateInterceptCell interceptCell
  rw [← image_comp]
  apply ((closedCell_isCompact 3 ((1+gamma)*tau)).image
    ((continuous_const.add M.continuous).comp coordinateEquiv.continuous)).isBounded.subset
  exact image_mono (openCell_subset_closedCell 3 ((1+gamma)*tau))

lemma framed_productCylinder_openBounded
    (M : RuledApproximation.Coordinates ≃L[ℝ] RuledApproximation.Plane)
    (p g : RuledApproximation.Plane) {h : ℝ} (hh : 0 < h) (tau gamma : ℝ) :
    (RuledApproximation.projectedCylinder h g
      ((fun x => p+M x) '' coordinateInterceptCell tau gamma)).openBounded := by
  have ho := framed_intercept_isOpen M p tau gamma
  have hb := framed_intercept_isBounded M p tau gamma
  exact ⟨RuledApproximation.projectedCylinder_base_open hh g ho,
    RuledApproximation.projectedCylinder_base_bounded hh g hb,
    RuledApproximation.projectedCylinder_base_measurable hh g ho.measurableSet⟩

lemma framed_productCylinder_cost
    (M : RuledApproximation.Coordinates ≃L[ℝ] RuledApproximation.Plane)
    (p g : RuledApproximation.Plane) (V : RuledApproximation.Plane → RuledApproximation.Plane)
    {h tau gamma eta : ℝ} (hh : 0 < h) (htau : 0 < tau) (htau1 : tau < 1)
    (hg : 0 ≤ gamma) (hpad : (1+gamma)*tau < 1) (heta : 0 ≤ eta)
    (hratio : areaRatio tau gamma ≤ 1+eta)
    (hV : ContinuousOn V ((fun x => p+M x) '' coordinateParameterCell tau))
    (hweight : ∀ q ∈ ((fun x => p+M x) '' coordinateParameterCell tau),
      RuledApproximation.physicalWeight h g ≤
        (1+eta)*RuledApproximation.physicalWeight h (V q)) :
    (RuledApproximation.projectedCylinder h g
      ((fun x => p+M x) '' coordinateInterceptCell tau gamma)).area ≤
      h*(1+eta)^2 * ∫ q in ((fun x => p+M x) '' coordinateParameterCell tau),
        RuledApproximation.physicalWeight h (V q) := by
  let G := (fun x => p+M x) '' coordinateParameterCell tau
  let U := (fun x => p+M x) '' coordinateInterceptCell tau gamma
  have hG : IsCompact G := framed_parameter_isCompact M p tau
  have hi : IntegrableOn (fun q => RuledApproximation.physicalWeight h (V q)) G :=
    ((RuledApproximation.physicalWeight_continuous h).comp_continuousOn hV).integrableOn_compact hG
  have hi' := setIntegral_ge_of_const_le_real hG.measurableSet hG.measure_ne_top
    hweight (hi.const_mul (1+eta))
  rw [integral_const_mul] at hi'
  have harea : volume.real U ≤ (1+eta)*volume.real G := by
    change volume.real ((fun x => p+M x) '' coordinateInterceptCell tau gamma) ≤ _
    rw [framed_intercept_area M p htau htau1 hg hpad]
    exact mul_le_mul_of_nonneg_right hratio measureReal_nonneg
  have hj : 0 ≤ RuledApproximation.physicalWeight h g :=
    (RuledApproximation.physicalWeight_pos h g).le
  have hc : 0 ≤ h*(1+eta) := mul_nonneg hh.le (by linarith)
  rw [RuledApproximation.projectedCylinder_area hh]
  change h * volume.real U * RuledApproximation.physicalWeight h g ≤ _
  calc
    h * volume.real U * RuledApproximation.physicalWeight h g
        ≤ h*((1+eta)*volume.real G)*RuledApproximation.physicalWeight h g :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left harea hh.le) hj
    _ = h*(1+eta)*(RuledApproximation.physicalWeight h g*volume.real G) := by ring
    _ ≤ h*(1+eta)*((1+eta)*∫ q in G, RuledApproximation.physicalWeight h (V q)) :=
          mul_le_mul_of_nonneg_left hi' hc
    _ = h*(1+eta)^2*∫ q in G, RuledApproximation.physicalWeight h (V q) := by ring

lemma uniform_weight_comparison {E : Type*} [PseudoMetricSpace E]
    {D : Set E} (hD : IsCompact D) {j : E → ℝ} (hj : ContinuousOn j D)
    (hjpos : ∀ p ∈ D, 0 < j p) {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ p ∈ D, ∀ q ∈ D,
      dist p q ≤ delta → j p ≤ (1+eta)*j q := by
  by_cases hne : D.Nonempty
  · obtain ⟨p₀,hp₀,hmin⟩ := hD.exists_isMinOn hne hj
    have hminpos := hjpos p₀ hp₀
    obtain ⟨delta,hdelta,huc⟩ := Metric.uniformContinuousOn_iff_le.mp
      (hD.uniformContinuousOn_of_continuous hj) (eta*j p₀) (mul_pos heta hminpos)
    refine ⟨delta,hdelta,?_⟩
    intro p hp q hq hpq
    have hdiff := huc p hp q hq hpq
    rw [Real.dist_eq] at hdiff
    have hupper := (abs_le.mp hdiff).2
    have hminq : j p₀ ≤ j q := hmin hq
    nlinarith [mul_le_mul_of_nonneg_left hminq heta.le]
  · refine ⟨1,by norm_num,?_⟩
    intro p hp
    exact (hne ⟨p,hp⟩).elim

lemma uniform_physicalWeight_comparison {D : Set RuledApproximation.Plane}
    (hD : IsCompact D) {V : RuledApproximation.Plane → RuledApproximation.Plane}
    (hV : ContinuousOn V D) (h : ℝ) {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ p ∈ D, ∀ q ∈ D,
      dist p q ≤ delta → RuledApproximation.physicalWeight h (V p) ≤
        (1+eta)*RuledApproximation.physicalWeight h (V q) :=
  uniform_weight_comparison hD
    ((RuledApproximation.physicalWeight_continuous h).comp_continuousOn hV)
    (fun p _ => RuledApproximation.physicalWeight_pos h (V p)) heta

private def scaledCoordinateFrame
    (L : Plane ≃L[ℝ] RuledApproximation.Plane) (rho : ℝ) (hrho : rho ≠ 0) :
    RuledApproximation.Coordinates ≃L[ℝ] RuledApproximation.Plane :=
  (coordinateEquiv.symm.trans L).trans
    (ContinuousLinearEquiv.smulLeft (R₁:=ℝ) (M₁:=RuledApproximation.Plane) (Units.mk0 rho hrho))

private lemma scaledCoordinateFrame_image
    (L : Plane ≃L[ℝ] RuledApproximation.Plane) (p : RuledApproximation.Plane)
    (rho : ℝ) (hrho : rho ≠ 0) (S : Set Plane) :
    (fun x => p+scaledCoordinateFrame L rho hrho x) '' (coordinateEquiv '' S) =
      (fun s => p+rho • L s) '' S := by
  rw [← image_comp]
  congr 1

lemma pair_frame_intercept_area
    (L : Plane ≃L[ℝ] RuledApproximation.Plane) (p : RuledApproximation.Plane)
    {rho tau gamma : ℝ} (hrho : 0 < rho) (htau : 0 < tau) (htau1 : tau < 1)
    (hg : 0 ≤ gamma) (hpad : (1+gamma)*tau < 1) :
    volume.real ((fun s => p+rho • L s) '' interceptCell tau gamma) =
      areaRatio tau gamma * volume.real ((fun s => p+rho • L s) '' parameterCell tau) := by
  have h := framed_intercept_area (scaledCoordinateFrame L rho (ne_of_gt hrho))
    p htau htau1 hg hpad
  simpa only [coordinateParameterCell,coordinateInterceptCell,scaledCoordinateFrame_image] using h

lemma pair_frame_parameter_isCompact
    (L : Plane ≃L[ℝ] RuledApproximation.Plane) (p : RuledApproximation.Plane)
    (rho tau : ℝ) : IsCompact ((fun s => p+rho • L s) '' parameterCell tau) :=
  (closedCell_isCompact 1 tau).image (by fun_prop)

lemma pair_frame_productCylinder_openBounded
    (L : Plane ≃L[ℝ] RuledApproximation.Plane) (p g : RuledApproximation.Plane)
    {rho h : ℝ} (hrho : 0 < rho) (hh : 0 < h) (tau gamma : ℝ) :
    (RuledApproximation.projectedCylinder h g
      ((fun s => p+rho • L s) '' interceptCell tau gamma)).openBounded := by
  have hc := framed_productCylinder_openBounded
    (scaledCoordinateFrame L rho (ne_of_gt hrho)) p g hh tau gamma
  simpa only [coordinateInterceptCell,scaledCoordinateFrame_image] using hc

lemma pair_frame_productCylinder_cost
    (L : Plane ≃L[ℝ] RuledApproximation.Plane) (p g : RuledApproximation.Plane)
    (V : RuledApproximation.Plane → RuledApproximation.Plane)
    {rho h tau gamma eta : ℝ} (hrho : 0 < rho) (hh : 0 < h)
    (htau : 0 < tau) (htau1 : tau < 1) (hg : 0 ≤ gamma)
    (hpad : (1+gamma)*tau < 1) (heta : 0 ≤ eta)
    (hratio : areaRatio tau gamma ≤ 1+eta)
    (hV : ContinuousOn V ((fun s => p+rho • L s) '' parameterCell tau))
    (hweight : ∀ q ∈ ((fun s => p+rho • L s) '' parameterCell tau),
      RuledApproximation.physicalWeight h g ≤
        (1+eta)*RuledApproximation.physicalWeight h (V q)) :
    (RuledApproximation.projectedCylinder h g
      ((fun s => p+rho • L s) '' interceptCell tau gamma)).area ≤
      h*(1+eta)^2 * ∫ q in ((fun s => p+rho • L s) '' parameterCell tau),
        RuledApproximation.physicalWeight h (V q) := by
  have heq := scaledCoordinateFrame_image L p rho (ne_of_gt hrho) (parameterCell tau)
  have hV' : ContinuousOn V ((fun x => p+scaledCoordinateFrame L rho (ne_of_gt hrho) x) ''
      coordinateParameterCell tau) := by
    simpa only [coordinateParameterCell,heq] using hV
  have hw' : ∀ q ∈ ((fun x => p+scaledCoordinateFrame L rho (ne_of_gt hrho) x) ''
      coordinateParameterCell tau), RuledApproximation.physicalWeight h g ≤
        (1+eta)*RuledApproximation.physicalWeight h (V q) := by
    simpa only [coordinateParameterCell,heq] using hweight
  have hc := framed_productCylinder_cost (scaledCoordinateFrame L rho (ne_of_gt hrho))
    p g V hh htau htau1 hg hpad heta hratio hV' hw'
  simpa only [coordinateParameterCell,coordinateInterceptCell,scaledCoordinateFrame_image] using hc

end ProductCells

end

end OAI
