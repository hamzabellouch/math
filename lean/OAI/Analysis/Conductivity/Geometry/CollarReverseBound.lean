import Mathlib
import OAI.Analysis.Conductivity.Geometry.CollarVolumeBound

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

def faceRayDensityLower (w : ℝ) : ℝ := w/(1+w^2)/(2*Real.pi)

lemma faceRayDensityLower_pos {w : ℝ} (hw : 0<w) : 0<faceRayDensityLower w := by
  unfold faceRayDensityLower
  positivity

lemma faceRayDensity_lower {w : ℝ} (hw : 0<w) (j : Fin 4) {b : ℝ} (hb : |b|≤1) :
    faceRayDensityLower w≤ faceRayDensity w j b := by
  have hsq : b^2≤1 := by
    have hh := mul_le_mul hb hb (abs_nonneg b) (by norm_num : (0:ℝ)≤1)
    simpa [←sq_abs b,pow_two] using hh
  have hp : 0<2*Real.pi := by positivity
  have he : (1/(1+(b/w)^2))/w=w/(w^2+b^2) := by
    field_simp
  have h0 : w/(1+w^2)≤(1/(1+(b/w)^2))/w := by
    rw [he]
    apply div_le_div_of_nonneg_left hw.le (by positivity)
    linarith
  have h1 : w/(1+w^2)≤w/(1+(w*b)^2) := by
    apply div_le_div_of_nonneg_left hw.le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg w)]
  unfold faceRayDensityLower faceRayDensity
  fin_cases j
  · exact div_le_div_of_nonneg_right h0 hp.le
  · exact div_le_div_of_nonneg_right h1 hp.le
  · exact div_le_div_of_nonneg_right h0 hp.le
  · exact div_le_div_of_nonneg_right h1 hp.le

lemma sourceExtended_jacobian_upper (i j : Fin 4) {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    {x : Fin 3 → ℝ} (hx : x∈sourceExtendedBox l r) :
    abs ((sourceCollarDerivative i j x).det)≤2 := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  have ht' : x 0∈Icc (-(1:ℝ)/100) (1/100) := ⟨hl.trans ht.1,ht.2.trans hr⟩
  have hR := sourceCollarRadius_extended j ht' hb
  rw [sourceCollarDerivative_det,abs_mul,abs_mul,abs_mul]
  rw [abs_neg,abs_of_pos (show 0<sourceLength by norm_num [sourceLength]),
    abs_of_nonneg (show 0≤ sourceCollarRadius j (x 0) (x 2) by linarith [hR.1]),
    abs_of_pos (show 0<sourceRadialWidth by norm_num [sourceRadialWidth,sourceHole]),
    abs_of_nonneg (show 0≤1-x 0 by linarith [ht'.2])]
  have hh := mul_le_mul hR.2 (show 1-x 0≤101/100 by linarith [ht'.1])
    (by linarith [ht'.2] : 0≤1-x 0) (by norm_num : (0:ℝ)≤2)
  norm_num [sourceLength,sourceRadialWidth,sourceHole]
  nlinarith

theorem sourceExtended_integral_upper {g : (Fin 3 → ℝ) → ℝ}
    (hg : Continuous g) (hn : ∀ y,0≤g y) (i j : Fin 4) {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    (∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,g y)≤
      2*(∫ x in sourceExtendedBox l r,g (sourceCollarPiece i j x)) := by
  rw [sourceExtended_integral i j hl hr,←integral_const_mul]
  apply setIntegral_mono_on
  · have hc : Continuous (fun x : Fin 3 → ℝ => abs ((sourceCollarDerivative i j x).det)) := by
      simp_rw [sourceCollarDerivative_det]
      unfold sourceCollarRadius squareFace
      fun_prop
    exact (hc.mul (hg.comp (sourceCollarPiece_contDiff i j).continuous)).continuousOn.integrableOn_compact isCompact_Icc
  · exact (continuous_const.mul (hg.comp (sourceCollarPiece_contDiff i j).continuous)).continuousOn.integrableOn_compact isCompact_Icc
  · exact measurableSet_Icc
  · intro x hx
    exact mul_le_mul_of_nonneg_right (sourceExtended_jacobian_upper i j hl hr hx) (hn _)

theorem integral_sourceAngular_lower {f : (Fin 3 → ℝ) → ℝ}
    (hf : Continuous f) (hn : ∀ z,0≤f z) (t : ℝ) :
    (faceRayDensityLower 1*faceRayDensityLower sourceRadialWidth)*
        (∑ i : Fin 4,∑ j : Fin 4,∫ a in (-1:ℝ)..1,∫ b in (-1:ℝ)..1,
          f (sourceCollarPiece i j ![t,a,b])) ≤
      ∫ x : UnitAddTorus (Fin 2),f (sourceAngularCollar t x) := by
  have hw : 0<sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hk₀ := (faceRayDensityLower_pos (w:=1) (by norm_num)).le
  have hk₁ := (faceRayDensityLower_pos hw).le
  rw [integral_unitTorus_faces (F:=fun x => f (sourceAngularCollar t x))
    (w₀:=1) (w₁:=sourceRadialWidth) (by norm_num) hw
    (hf.comp (continuous_sourceAngularCollar t)),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact (continuous_const.mul (continuous_parametric_unitInterval
      (f:=fun a b => f (sourceCollarPiece i j ![t,a,b]))
      (hf.comp (sourceAngularFace_continuous t i j)))).intervalIntegrable _ _
  · exact ((continuous_parametric_unitInterval
      (continuous_torusFaceTerm 1 sourceRadialWidth
        (hf.comp (continuous_sourceAngularCollar t)) i j)).mul
      (continuous_faceRayDensity 1 i)).intervalIntegrable _ _
  · intro a ha
    have hinner : faceRayDensityLower sourceRadialWidth*
        (∫ b in (-1:ℝ)..1,f (sourceCollarPiece i j ![t,a,b])) ≤
        ∫ b in (-1:ℝ)..1,
          torusFaceTerm 1 sourceRadialWidth (fun x => f (sourceAngularCollar t x)) i j a b := by
      rw [←intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact (continuous_const.mul ((hf.comp (sourceAngularFace_continuous t i j)).comp
          (continuous_const.prodMk continuous_id))).intervalIntegrable _ _
      · exact ((continuous_torusFaceTerm 1 sourceRadialWidth
          (hf.comp (continuous_sourceAngularCollar t)) i j).comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
      · intro b hb
        dsimp only [torusFaceTerm]
        rw [sourceAngular_face t a b i j (abs_le.mpr ha) (abs_le.mpr hb),mul_comm]
        exact mul_le_mul_of_nonneg_left (faceRayDensity_lower hw j (abs_le.mpr hb)) (hn _)
    have hnint : 0≤ ∫ b in (-1:ℝ)..1,f (sourceCollarPiece i j ![t,a,b]) :=
      intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => hn _)
    calc
      _ = (faceRayDensityLower sourceRadialWidth*
          (∫ b in (-1:ℝ)..1,f (sourceCollarPiece i j ![t,a,b])))*faceRayDensityLower 1 := by ring
      _ ≤ _ := mul_le_mul hinner (faceRayDensity_lower (by norm_num) i (abs_le.mpr ha))
        hk₀ ((mul_nonneg hk₁ hnint).trans hinner)

theorem sourceAngular_volume_reverse {g : (Fin 3 → ℝ) → ℝ}
    (hg : Continuous g) (hn : ∀ y,0≤g y) {l r : ℝ}
    (hlr : l≤r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    (∑ i : Fin 4,∑ j : Fin 4,∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,g y)≤
      (2/(faceRayDensityLower 1*faceRayDensityLower sourceRadialWidth))*
        (∫ t in l..r,∫ x : UnitAddTorus (Fin 2),g (sourceAngularCollar t x)) := by
  let k := faceRayDensityLower 1*faceRayDensityLower sourceRadialWidth
  have hk : 0<k := mul_pos (faceRayDensityLower_pos (by norm_num))
    (faceRayDensityLower_pos (by norm_num [sourceRadialWidth,sourceHole]))
  have hcont : Continuous (fun t : ℝ => ∫ x : UnitAddTorus (Fin 2),g (sourceAngularCollar t x)) := by
    have hcs : Continuous (fun p : ℝ×UnitAddTorus (Fin 2) => sourceAngularCollar p.1 p.2) := by
      simpa only [zero_add] using continuous_sourceAngular 0
    have hh := continuous_parametric_integral_of_continuous (μ:=volume)
      (f:=fun t (x : UnitAddTorus (Fin 2)) => g (sourceAngularCollar t x))
      (hg.comp hcs) (s:=univ) isCompact_univ
    simpa using hh
  have hsum : Continuous (fun t : ℝ => ∑ i : Fin 4,∑ j : Fin 4,
      ∫ a in (-1:ℝ)..1,∫ b in (-1:ℝ)..1,g (sourceCollarPiece i j ![t,a,b])) :=
    continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => continuous_collarFace_integral hg i j))
  have Hint : k*(∑ i : Fin 4,∑ j : Fin 4,
      ∫ x in sourceExtendedBox l r,g (sourceCollarPiece i j x))≤
      ∫ t in l..r,∫ x : UnitAddTorus (Fin 2),g (sourceAngularCollar t x) := by
    have hh := intervalIntegral.integral_mono_on (μ:=volume) hlr
      ((continuous_const.mul hsum).intervalIntegrable l r)
      (hcont.intervalIntegrable l r) (fun t _ => integral_sourceAngular_lower hg hn t)
    simp only [Pi.mul_apply] at hh
    rw [intervalIntegral.integral_const_mul] at hh
    convert hh using 2
    rw [intervalIntegral.integral_finsetSum (fun i _ =>
      (continuous_finsetSum _ (fun j _ => continuous_collarFace_integral hg i j)).intervalIntegrable l r)]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum (fun j _ => (continuous_collarFace_integral hg i j).intervalIntegrable l r)]
    apply Finset.sum_congr rfl
    intro j _
    exact integral_sourceExtendedBox (hg.comp (sourceCollarPiece_contDiff i j).continuous) hlr
  calc
    _ ≤ ∑ i : Fin 4,∑ j : Fin 4,2*(∫ x in sourceExtendedBox l r,g (sourceCollarPiece i j x)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact sourceExtended_integral_upper hg hn i j hl hr
    _ = (2/k)*(k*(∑ i : Fin 4,∑ j : Fin 4,
        ∫ x in sourceExtendedBox l r,g (sourceCollarPiece i j x))) := by
      simp_rw [←Finset.mul_sum]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left Hint (by positivity)

end ScalarConductivity

end

end OAI
