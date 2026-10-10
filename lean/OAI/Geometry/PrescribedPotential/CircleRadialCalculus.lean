import Mathlib
import OAI.Geometry.PrescribedPotential.CircleSubmeanCalculus

namespace OAI

/-! Circle Radial Calculus. -/

section

 

noncomputable section
open Set Filter Topology Metric MeasureTheory
open scoped ContDiff
namespace PotentialABP

private def v (θ : ℝ) : ℂ := circleMap 0 1 θ
private def w (θ : ℝ) : ℂ := v θ * Complex.I

private lemma dv (θ : ℝ) : HasDerivAt v (w θ) θ := hasDerivAt_circleMap 0 1 θ
private lemma dw (θ : ℝ) : HasDerivAt w (-v θ) θ := by
  convert (dv θ).mul_const Complex.I using 1 <;> first | rfl | simp [w, mul_assoc]

private lemma cv : Continuous v := continuous_circleMap 0 1
private lemma cw : Continuous w := cv.mul continuous_const

 
def circleIntegralReal (f : ℂ → ℝ) (c : ℂ) (r : ℝ) : ℝ :=
  ∫ θ in 0..2*Real.pi, f (c + r • v θ)
def radialIntegral (f : ℂ → ℝ) (c : ℂ) (r : ℝ) : ℝ :=
  ∫ θ in 0..2*Real.pi, fderiv ℝ f (c + r • v θ) (v θ)
def secondRadialIntegral (f : ℂ → ℝ) (c : ℂ) (r : ℝ) : ℝ :=
  ∫ θ in 0..2*Real.pi, fderiv ℝ (fderiv ℝ f) (c + r • v θ) (v θ) (v θ)
def angularHessianIntegral (f : ℂ → ℝ) (c : ℂ) (r : ℝ) : ℝ :=
  ∫ θ in 0..2*Real.pi, fderiv ℝ (fderiv ℝ f) (c + r • v θ) (w θ) (w θ)

lemma circleIntegralReal_eq_circleAverage (f : ℂ → ℝ) (c : ℂ) (r : ℝ) :
    circleIntegralReal f c r = 2*Real.pi * Real.circleAverage f c r := by
  unfold circleIntegralReal Real.circleAverage
  simp only [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity : (2:ℝ)*Real.pi ≠ 0), one_mul]
  congr 1
  funext θ
  congr 1
  simp [v, circleMap, Complex.real_smul]

lemma circleIntegralReal_hasDerivAt {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℂ) (r : ℝ) :
    HasDerivAt (circleIntegralReal f c) (radialIntegral f c r) r := by
  refine hasDerivAt_intervalIntegral_continuous
    (F := fun s θ => f (c + s • v θ))
    (F' := fun s θ => fderiv ℝ f (c + s • v θ) (v θ)) ?_ ?_ ?_ 0 (2*Real.pi) r
  · exact hf.continuous.comp (continuous_const.add (continuous_fst.smul (cv.comp continuous_snd)))
  · exact ((hf.continuous_fderiv (by simp)).comp
      (continuous_const.add (continuous_fst.smul (cv.comp continuous_snd)))).clm_apply (cv.comp continuous_snd)
  · intro s θ
    simpa only [one_smul, Function.comp_def, id_eq] using
      (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
        (((hasDerivAt_id s).smul_const (v θ)).const_add c)

lemma radialIntegral_hasDerivAt {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℂ) (r : ℝ) :
    HasDerivAt (radialIntegral f c) (secondRadialIntegral f c r) r := by
  have hdf := hf.fderiv_right (m := ∞) (by simp)
  refine hasDerivAt_intervalIntegral_continuous
    (F := fun s θ => fderiv ℝ f (c + s • v θ) (v θ))
    (F' := fun s θ => fderiv ℝ (fderiv ℝ f) (c + s • v θ) (v θ) (v θ))
    ?_ ?_ ?_ 0 (2*Real.pi) r
  · exact (hdf.continuous.comp
      (continuous_const.add (continuous_fst.smul (cv.comp continuous_snd)))).clm_apply (cv.comp continuous_snd)
  · exact (((hdf.continuous_fderiv (by simp)).comp
      (continuous_const.add (continuous_fst.smul (cv.comp continuous_snd)))).clm_apply
      (cv.comp continuous_snd)).clm_apply (cv.comp continuous_snd)
  · intro s θ
    have h := ((hdf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
      (((hasDerivAt_id s).smul_const (v θ)).const_add c)).clm_apply (hasDerivAt_const s (v θ))
    simpa only [one_smul, Function.comp_def, id_eq, map_zero, add_zero] using h

lemma radialIntegral_eq_radius_angular {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℂ) (r : ℝ) :
    radialIntegral f c r = r * angularHessianIntegral f c r := by
  have hdf := hf.fderiv_right (m := ∞) (by simp)
  let T : ℝ → ℝ := fun θ => fderiv ℝ f (c + r • v θ) (w θ)
  let T' : ℝ → ℝ := fun θ => r * fderiv ℝ (fderiv ℝ f) (c + r • v θ) (w θ) (w θ)
    - fderiv ℝ f (c + r • v θ) (v θ)
  have ht (θ : ℝ) : HasDerivAt T (T' θ) θ := by
    have h := ((hdf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt θ
      (((dv θ).const_smul r).const_add c)).clm_apply (dw θ)
    simpa only [T, T', Function.comp_def, map_smul, map_neg, smul_eq_mul, sub_eq_add_neg, Pi.smul_apply, smul_apply] using h
  have hct : Continuous T' := by
    apply Continuous.sub
    · exact continuous_const.mul (((hdf.continuous_fderiv (by simp)).comp
        (continuous_const.add (cv.const_smul r))).clm_apply cw |>.clm_apply cw)
    · exact (hdf.continuous.comp (continuous_const.add (cv.const_smul r))).clm_apply cv
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => ht θ) (hct.intervalIntegrable 0 (2*Real.pi))
  have hp : T (2*Real.pi) = T 0 := by
    have hv : v (2*Real.pi) = v 0 := by
      simpa only [v, zero_add] using periodic_circleMap 0 1 0
    simp only [T, w, hv]
  rw [hp, sub_self] at he
  have hc1 : Continuous (fun θ => fderiv ℝ (fderiv ℝ f) (c + r • v θ) (w θ) (w θ)) :=
    (((hdf.continuous_fderiv (by simp)).comp
      (continuous_const.add (cv.const_smul r))).clm_apply cw).clm_apply cw
  have hc2 : Continuous (fun θ => fderiv ℝ f (c + r • v θ) (v θ)) :=
    (hdf.continuous.comp (continuous_const.add (cv.const_smul r))).clm_apply cv
  dsimp only [T'] at he
  have hi1 : IntervalIntegrable (fun θ => r * fderiv ℝ (fderiv ℝ f)
      (c + r • v θ) (w θ) (w θ)) volume 0 (2*Real.pi) :=
    (continuous_const.mul hc1).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi1 (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul] at he
  exact (sub_eq_zero.mp he).symm

lemma radialIntegral_continuous {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℂ) :
    Continuous (radialIntegral f c) :=
  continuous_iff_continuousAt.mpr (fun r => (radialIntegral_hasDerivAt hf c r).continuousAt)
lemma circleIntegralReal_continuous {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℂ) :
    Continuous (circleIntegralReal f c) :=
  continuous_iff_continuousAt.mpr (fun r => (circleIntegralReal_hasDerivAt hf c r).continuousAt)

private lemma hessian_circle_pair (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (θ : ℝ) :
    B (v θ) (v θ) + B (w θ) (w θ) = B 1 1 + B Complex.I Complex.I := by
  have hv : v θ = Real.cos θ • (1:ℂ) + Real.sin θ • Complex.I := by
    apply Complex.ext <;> simp [v, circleMap_zero_re, circleMap_zero_im, -Complex.ofReal_cos, -Complex.ofReal_sin]
  have hw : w θ = (-Real.sin θ) • (1:ℂ) + Real.cos θ • Complex.I := by
    apply Complex.ext <;> simp [w, v, circleMap_zero_re, circleMap_zero_im, Complex.mul_re, Complex.mul_im, -Complex.ofReal_cos, -Complex.ofReal_sin]
  rw [hv, hw]
  calc
    _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) * (B 1 1 + B Complex.I Complex.I) := by
      simp only [map_add, map_smul, add_apply,
        smul_apply, smul_eq_mul]
      ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]

 

theorem smooth_circle_submean {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (htrace : ∀ z ∈ closedBall c R,
      0 ≤ fderiv ℝ (fderiv ℝ f) z 1 1 +
        fderiv ℝ (fderiv ℝ f) z Complex.I Complex.I) :
    f c ≤ Real.circleAverage f c R := by
  have hdf := hf.fderiv_right (m := ∞) (by simp)
  have hpos (r : ℝ) (hr : r ∈ Icc 0 R) :
      0 ≤ secondRadialIntegral f c r + angularHessianIntegral f c r := by
    have hc1 : Continuous (fun θ => fderiv ℝ (fderiv ℝ f) (c + r • v θ) (v θ) (v θ)) :=
      (((hdf.continuous_fderiv (by simp)).comp
        (continuous_const.add (cv.const_smul r))).clm_apply cv).clm_apply cv
    have hc2 : Continuous (fun θ => fderiv ℝ (fderiv ℝ f) (c + r • v θ) (w θ) (w θ)) :=
      (((hdf.continuous_fderiv (by simp)).comp
        (continuous_const.add (cv.const_smul r))).clm_apply cw).clm_apply cw
    dsimp only [secondRadialIntegral, angularHessianIntegral]
    rw [← intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
    apply intervalIntegral.integral_nonneg_of_forall (by positivity)
    intro θ
    rw [hessian_circle_pair]
    apply htrace
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      v, norm_circleMap_zero, abs_one, mul_one, Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact hr.2
  let J : ℝ → ℝ := fun r => r * radialIntegral f c r
  have hdJ (r : ℝ) : HasDerivAt J
      (radialIntegral f c r + r * secondRadialIntegral f c r) r := by
    have hh := (hasDerivAt_id r).mul (radialIntegral_hasDerivAt hf c r)
    change HasDerivAt (fun s => s * radialIntegral f c s) _ r at hh
    simpa only [J, id_eq, one_mul] using hh
  have hmJ : MonotoneOn J (Icc 0 R) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 R)
      ((continuous_id.mul (radialIntegral_continuous hf c)).continuousOn)
      (fun r _ => (hdJ r).hasDerivWithinAt)
    intro r hr
    have hr' := interior_subset hr
    rw [radialIntegral_eq_radius_angular hf, ← mul_add]
    exact mul_nonneg hr'.1 (by simpa only [add_comm] using hpos r hr')
  have hmF : MonotoneOn (circleIntegralReal f c) (Icc 0 R) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 R)
      (circleIntegralReal_continuous hf c).continuousOn
      (fun r _ => (circleIntegralReal_hasDerivAt hf c r).hasDerivWithinAt)
    intro r hr
    have hr' : r ∈ Ioo 0 R := by simpa only [interior_Icc] using hr
    have hj := hmJ ⟨le_rfl,hR⟩ ⟨hr'.1.le,hr'.2.le⟩ hr'.1.le
    simp only [J, zero_mul] at hj
    nlinarith [hr'.1]
  have he := hmF ⟨le_rfl,hR⟩ ⟨hR,le_rfl⟩ hR
  have hF0 : circleIntegralReal f c 0 = 2*Real.pi*f c := by
    simp [circleIntegralReal]
  have hFR : Real.circleAverage f c R = (2*Real.pi)⁻¹ * circleIntegralReal f c R := by
    unfold Real.circleAverage circleIntegralReal
    congr 2
    funext θ
    congr 1
    simp [v, circleMap, Complex.real_smul]
  rw [hF0] at he
  rw [hFR]
  exact (le_inv_mul_iff₀ (by positivity : 0 < 2*Real.pi)).mpr (by simpa only [mul_comm] using he)

end PotentialABP

end
end

end OAI
