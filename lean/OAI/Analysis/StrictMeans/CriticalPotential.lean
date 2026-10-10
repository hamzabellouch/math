import OAI.Analysis.StrictMeans.BoundaryEscape

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

def logPotential (k : ℝ) (F : ℂ → ℂ) (ξ z : ℂ) : ℝ :=
  k * Real.log z.im - Real.log ‖F z - ξ‖

lemma complex_log_norm_fderiv {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (hne : F z ≠ 0) :
    fderiv ℝ (fun w => Real.log ‖F w‖) z =
      Complex.reCLM.comp ((ContinuousLinearMap.toSpanSingleton ℂ (deriv F z / F z)).restrictScalars ℝ) := by
  have hd := hF.hasDerivAt.complexToReal_fderiv
  have hn : ‖F z‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hne)
  have hh := ((hd.norm_sq).log hn).const_mul (1/2)
  have he : (fun w => (1/2:ℝ) * Real.log (‖F w‖^2)) = (fun w => Real.log ‖F w‖) := by
    funext w
    rw [Real.log_pow]
    ring
  rw [he] at hh
  rw [hh.fderiv]
  ext v
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    Complex.reCLM_apply, innerSL_apply_apply, one_apply_eq_self]
  simp only [Complex.inner, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, Complex.conj_re, Complex.conj_im]
  rw [← Complex.normSq_eq_norm_sq]
  field_simp
  ring

lemma logPotential_differentiableAt {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : DifferentiableAt ℂ F z) (hne : F z ≠ ξ) :
    DifferentiableAt ℝ (logPotential k F ξ) z := by
  exact ((Complex.imCLM.differentiableAt).log hz.ne').const_mul k |>.sub
    (((hF.restrictScalars (𝕜 := ℝ)).sub_const ξ).norm ℝ (sub_ne_zero.mpr hne) |>.log (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)))

lemma logPotential_fderiv_apply {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : DifferentiableAt ℂ F z) (hne : F z ≠ ξ) (v : ℂ) :
    fderiv ℝ (logPotential k F ξ) z v =
      k / z.im * v.im - ((deriv F z / (F z-ξ))*v).re := by
  have hu : HasFDerivAt (fun w : ℂ => Real.log w.im) ((z.im)⁻¹ • Complex.imCLM) z := by
    simpa only [Complex.imCLM_apply] using (Complex.imCLM.hasFDerivAt (x := z)).log hz.ne'
  have h1 := hu.const_mul k
  have h2 : DifferentiableAt ℝ (fun w => Real.log ‖F w-ξ‖) z :=
    (((hF.restrictScalars (𝕜 := ℝ)).sub_const ξ).norm ℝ (sub_ne_zero.mpr hne)).log (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))
  change (fderiv ℝ ((fun w => k * Real.log w.im) - (fun w => Real.log ‖F w-ξ‖)) z) v = _
  rw [fderiv_sub h1.differentiableAt h2, h1.fderiv,
    complex_log_norm_fderiv (hF.sub_const ξ) (sub_ne_zero.mpr hne)]
  simp only [sub_apply, smul_apply, smul_eq_mul, Complex.imCLM_apply,
    ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    deriv_sub_const]
  rw [mul_comm v (deriv F z / (F z-ξ))]
  congr 1
  ring

lemma logPotential_critical_iff {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hk : k ≠ 0) (hz : 0 < z.im) (hF : DifferentiableAt ℂ F z) (hne : F z ≠ ξ) :
    fderiv ℝ (logPotential k F ξ) z = 0 ↔ criticalMap k F z = ξ := by
  have hkC : (k:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  have hyC : (z.im:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hFC : F z-ξ ≠ 0 := sub_ne_zero.mpr hne
  let r : ℂ := deriv F z / (F z-ξ)
  have hx := logPotential_fderiv_apply (k := k) hz hF hne 1
  have hy := logPotential_fderiv_apply (k := k) hz hF hne I
  have hrc : fderiv ℝ (logPotential k F ξ) z = 0 ↔ r = -I * (k:ℂ)/(z.im:ℂ) := by
    constructor
    · intro h
      rw [h] at hx hy
      apply Complex.ext
      · simp only [zero_apply, one_im, mul_zero, zero_sub, mul_one] at hx
        simp only [Complex.div_ofReal_re, neg_mul, neg_re, Complex.mul_re,
          I_re, ofReal_re, I_im, ofReal_im, zero_mul, mul_zero, sub_self, neg_zero, zero_div]
        dsimp [r]
        linarith
      · simp only [zero_apply, I_im, mul_one, mul_I_re, sub_neg_eq_add] at hy
        simp only [Complex.div_ofReal_im, neg_mul, neg_im, Complex.mul_im,
          I_re, ofReal_re, I_im, ofReal_im, mul_zero, one_mul, zero_add, neg_div]
        dsimp [r]
        linarith
    · intro h
      ext v
      rw [zero_apply, logPotential_fderiv_apply hz hF hne]
      change k/z.im*v.im-(r*v).re=0
      rw [h]
      simp [Complex.div_re, Complex.div_im, mul_re, mul_im]
      field_simp
      ring
  rw [hrc]
  dsimp [r,criticalMap]
  constructor
  · intro h
    have he := (div_eq_iff hFC).mp h
    rw [he]
    field_simp
    ring_nf
    simp [Complex.I_sq]
  · intro h
    apply (div_eq_iff hFC).mpr
    apply_fun (fun w : ℂ => w * (k:ℂ)) at h
    field_simp at h ⊢
    linear_combination (norm := ring_nf) I*h
    simp [Complex.I_sq]

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

def criticalHeight (k : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  k * z.im ^ (k-1) * ‖(deriv F z)⁻¹‖

lemma criticalMap_ne_image {k : ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hk : k ≠ 0) (hz : 0 < z.im) (hF : deriv F z ≠ 0) :
    criticalMap k F z ≠ F z := by
  intro h
  have hh : I * (z.im : ℂ) * deriv F z / (k : ℂ) = 0 := by
    have := sub_eq_self.mp h
    exact this
  exact (div_ne_zero (mul_ne_zero (mul_ne_zero I_ne_zero
    (Complex.ofReal_ne_zero.mpr hz.ne')) hF) (Complex.ofReal_ne_zero.mpr hk)) hh

lemma criticalMap_sub_image {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hg : criticalMap k F z = ξ) :
    F z - ξ = I * (z.im : ℂ) * deriv F z / (k : ℂ) := by
  dsimp [criticalMap] at hg
  linear_combination hg

lemma criticalHeight_pos {k : ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hk : 0 < k) (hz : 0 < z.im) (hF : deriv F z ≠ 0) :
    0 < criticalHeight k F z := by
  exact mul_pos (mul_pos hk (Real.rpow_pos_of_pos hz _)) (norm_pos_iff.mpr (inv_ne_zero hF))

lemma criticalHeight_value {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hk : 0 < k) (hz : 0 < z.im) (hg : criticalMap k F z = ξ) :
    z.im ^ k / ‖F z - ξ‖ = criticalHeight k F z := by
  rw [criticalMap_sub_image hg]
  simp only [norm_div, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hz, abs_of_pos hk, criticalHeight, norm_inv]
  rw [Real.rpow_sub hz, Real.rpow_one]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

lemma criticalHeight_superlevel {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ} {h : ℝ}
    (hk : 0 < k) (hz : 0 < z.im) (hF : deriv F z ≠ 0) (hh : 0 < h)
    (hg : criticalMap k F z = ξ) :
    z ∈ potentialSuperlevel k F ξ h ↔ h ≤ criticalHeight k F z := by
  have hn : 0 < ‖F z - ξ‖ := by
    apply norm_pos_iff.mpr
    apply sub_ne_zero.mpr
    intro he
    exact criticalMap_ne_image hk.ne' hz hF (hg.trans he.symm)
  rw [← criticalHeight_value hk hz hg]
  change (0 < z.im ∧ ‖F z - ξ‖ ≤ z.im ^ k / h) ↔ _
  rw [and_iff_right hz, le_div_iff₀ hh, le_div_iff₀ hn]
  rw [mul_comm]

lemma continuous_criticalMap (k : ℝ) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => criticalMap k (halfPlaneFunction p.1) p.2) := by
  exact continuous_halfPlaneFunction.sub ((continuous_const.mul
    (Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.comp continuous_snd))).mul
    continuous_halfPlaneFunction_deriv |>.div_const _)

lemma continuous_criticalHeight (k : ℝ) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => criticalHeight k (halfPlaneFunction p.1) p.2) := by
  apply (continuous_const.mul ?_).mul ?_
  · exact (UpperHalfPlane.continuous_im.comp continuous_snd).rpow_const
      (fun p => Or.inl p.2.im_ne_zero)
  · exact (continuous_halfPlaneFunction_deriv.inv₀
      (fun p => halfPlaneFunction_deriv_ne_zero p.1 p.2.im_pos)).norm

lemma criticalMap_contDiffAt (k : ℝ) (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ⊤ (criticalMap k (halfPlaneFunction f)) z := by
  have ha : AnalyticAt ℂ (halfPlaneFunction f) z :=
    (halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz)
  exact (ha.restrictScalars (𝕜 := ℝ)).contDiffAt.sub
    ((contDiffAt_const.mul ((Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).contDiffAt)).mul
      (ha.deriv.restrictScalars (𝕜 := ℝ)).contDiffAt |>.div_const _)

lemma jacobianExpression_zero_iff (k : ℝ) (hk : k ≠ 0) (f : DiskFamily)
    {z : ℂ} (hz : 0 < z.im) :
    jacobianExpression k (halfPlaneFunction f) z = 0 ↔
      (fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det = 0 := by
  have ha : AnalyticAt ℂ (halfPlaneFunction f) z :=
    (halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz)
  rw [← normalizedJacobian_eq hk ha.differentiableAt ha.deriv.differentiableAt
    (halfPlaneFunction_deriv_ne_zero f hz), normalizedJacobian]
  rw [div_eq_zero_iff]
  simp [halfPlaneFunction_deriv_ne_zero f hz]

end
end StrictInverseFirstPower

end

end OAI
