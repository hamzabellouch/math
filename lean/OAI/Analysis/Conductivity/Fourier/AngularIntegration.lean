import Mathlib
import OAI.Analysis.Conductivity.Fourier.AngularNormalTrace

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

theorem integral_circle_faces {w : ℝ} (hw : 0<w) {F : UnitAddCircle → ℝ}
    (hF : Continuous F) :
    (∫ θ,F θ ∂AddCircle.haarAddCircle)=
      ∑ j : Fin 4,∫ b in (-1:ℝ)..1,
        F ((faceRayAngle w j b:ℝ):UnitAddCircle)*faceRayDensity w j b := by
  have hc : Continuous (fun a : ℝ => F (a:UnitAddCircle)) :=
    hF.comp (AddCircle.continuous_mk' 1)
  have hh (j : Fin 4) :
      (∫ b in (-1:ℝ)..1,F ((faceRayAngle w j b:ℝ):UnitAddCircle)*faceRayDensity w j b)=
      ∫ a in faceRayAngle w j (-1)..faceRayAngle w j 1,F (a:UnitAddCircle) := by
    exact intervalIntegral.integral_comp_mul_deriv
      (fun b _ => hasDerivAt_faceRayAngle w j b) (continuous_faceRayDensity w j).continuousOn hc
  simp_rw [hh]
  have he := faceRayAngle_endpoints hw
  rw [AddCircle.integral_haarAddCircle]
  simp only [inv_one,one_smul]
  rw [←AddCircle.intervalIntegral_preimage 1 (faceRayAngle w 0 (-1))]
  rw [Fin.sum_univ_four,←he.2]
  have h0 := he.1 (0:Fin 3)
  have h1 := he.1 (1:Fin 3)
  have h2 := he.1 (2:Fin 3)
  change faceRayAngle w 0 1=faceRayAngle w 1 (-1) at h0
  change faceRayAngle w 1 1=faceRayAngle w 2 (-1) at h1
  change faceRayAngle w 2 1=faceRayAngle w 3 (-1) at h2
  rw [←h0,←h1,←h2]
  rw [intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]

theorem integral_rectangularRay_le {w : ℝ} (hw : 0<w) (hw' : w≤1)
    {f : (Fin 2 → ℝ) → ℝ} (hf : Continuous f)
    (hn : ∀ z,0≤f z) :
    (∫ θ,f (rectangularRay w θ) ∂AddCircle.haarAddCircle)≤
      ((1/w)/(2*Real.pi))*∑ j : Fin 4,∫ b in (-1:ℝ)..1,
        f ![w*squareFace j b 0,squareFace j b 1] := by
  rw [integral_circle_faces (F:=fun θ => f (rectangularRay w θ)) hw (hf.comp (continuous_rectangularRay hw hw'))]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · have ha : Continuous (faceRayAngle w j) := continuous_iff_continuousAt.mpr
      (fun b => (hasDerivAt_faceRayAngle w j b).continuousAt)
    exact ((hf.comp (continuous_rectangularRay hw hw')).comp
      ((AddCircle.continuous_mk' 1).comp ha)).mul
        (continuous_faceRayDensity w j) |>.intervalIntegrable _ _
  · have hc : Continuous (fun b : ℝ => ![w*squareFace j b 0,squareFace j b 1]) := by
      apply continuous_pi
      intro i
      fin_cases i
      · unfold squareFace; fun_prop
      · unfold squareFace; fun_prop
    exact (continuous_const.mul (hf.comp hc)).intervalIntegrable _ _
  · intro b hb
    rw [faceRayAngle_image hw j (abs_le.mpr hb)]
    exact (mul_le_mul_of_nonneg_left (faceRayDensity_bounds hw hw' j b).2
      (hn ![w*squareFace j b 0,squareFace j b 1])).trans_eq (mul_comm _ _)

end ScalarConductivity

end

end OAI
