import OAI.Analysis.StrictMeans.SmoothMorseIndex

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

lemma realHessian_eq_second {u : ℂ → ℝ} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) (v w : ℂ) :
    realHessian u z v w = Grid.second u z v w := by
  have hd := (hu.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero
  unfold realHessian Grid.second
  rw [(hd.hasFDerivAt.clm_apply (hasFDerivAt_const w z)).fderiv]
  simp

lemma squaredReciprocalPotential_eq_sq {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ} (hz : 0<z.im) :
    squaredReciprocalPotential k F ξ z = (‖F z-ξ‖ / z.im^k)^2 := by
  unfold squaredReciprocalPotential
  rw [show -2*k=-(k*2) by ring,Real.rpow_neg hz.le,
    Real.rpow_mul hz.le k 2,Real.rpow_two,div_pow,div_eq_mul_inv]

lemma squaredReciprocalPotential_sublevel {k : ℝ} {F : ℂ → ℂ} {ξ : ℂ} {h : ℝ} (hh : 0<h) :
    {z : ℂ | 0<z.im ∧ squaredReciprocalPotential k F ξ z≤(1/h)^2} =
      potentialSuperlevel k F ξ h := by
  ext z
  change (0<z.im ∧ _≤_) ↔ (0<z.im ∧ ‖F z-ξ‖≤z.im^k/h)
  apply and_congr_right
  intro hz
  rw [squaredReciprocalPotential_eq_sq hz,
    sq_le_sq₀ (div_nonneg (norm_nonneg _) (Real.rpow_pos_of_pos hz k).le) (one_div_nonneg.mpr hh.le),
    div_le_iff₀ (Real.rpow_pos_of_pos hz k)]
  ring_nf

lemma squaredReciprocalPotential_lt_sublevel {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ} {h : ℝ}
    (hz : 0<z.im) (hh : 0<h) :
    squaredReciprocalPotential k F ξ z<(1/h)^2 ↔ ‖F z-ξ‖<z.im^k/h := by
  rw [squaredReciprocalPotential_eq_sq hz,
    sq_lt_sq₀ (div_nonneg (norm_nonneg _) (Real.rpow_pos_of_pos hz k).le) (one_div_nonneg.mpr hh.le),
    div_lt_iff₀ (Real.rpow_pos_of_pos hz k)]
  ring_nf

lemma squaredReciprocalPotential_fderiv_off_pole {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0<z.im) (hF : AnalyticAt ℂ F z) (hp : F z≠ξ) :
    fderiv ℝ (squaredReciprocalPotential k F ξ) z =
      (-2*squaredReciprocalPotential k F ξ z) • fderiv ℝ (logPotential k F ξ) z := by
  have he : squaredReciprocalPotential k F ξ =ᶠ[𝓝 z]
      (fun t=>Real.exp (-2*logPotential k F ξ t)) := by
    filter_upwards [isOpen_halfPlane.mem_nhds hz,hF.continuousAt.eventually_ne hp] with t ht hpt
    exact squaredReciprocalPotential_eq_exp ht hpt
  rw [he.fderiv_eq]
  rw [(((logPotential_differentiableAt hz hF.differentiableAt hp).hasFDerivAt.const_mul (-2)).exp).fderiv]
  rw [← squaredReciprocalPotential_eq_exp hz hp]
  ext v
  simp
  ring

lemma squaredReciprocalPotential_critical_iff {k : ℝ} (hk : k≠0)
    {F : ℂ → ℂ} {ξ z : ℂ} (hz : 0<z.im) (hF : AnalyticAt ℂ F z) :
    fderiv ℝ (squaredReciprocalPotential k F ξ) z=0 ↔
      F z=ξ ∨ criticalMap k F z=ξ := by
  by_cases hp : F z=ξ
  · simp [hp,squaredReciprocalPotential_fderiv_pole hz hF hp]
  rw [or_iff_right hp,squaredReciprocalPotential_fderiv_off_pole hz hF hp,
    smul_eq_zero,or_iff_right (mul_ne_zero (by norm_num) (by rw [squaredReciprocalPotential_eq_exp hz hp]; exact (Real.exp_pos _).ne'))]
  exact logPotential_critical_iff hk hz hF.differentiableAt hp

lemma squaredReciprocalPotential_hessian_det {k : ℝ} (hk : k≠0)
    {F : ℂ → ℂ} {ξ z : ℂ} (hz : 0<z.im) (hF : AnalyticAt ℂ F z)
    (hd : deriv F z≠0) (hg : criticalMap k F z=ξ) :
    Grid.hessianDet (squaredReciprocalPotential k F ξ) z =
      -(4*(squaredReciprocalPotential k F ξ z)^2*(k^4/z.im^4))*jacobianExpression k F z := by
  have hp : F z≠ξ := fun he=>criticalMap_ne_image hk hz hd (hg.trans he.symm)
  have hu := (squaredReciprocalPotential_contDiffAt (k:=k) (ξ:=ξ) hz hF).of_le (show (2 : WithTop ℕ∞)≤⊤ by simp)
  have hl := logPotential_contDiffAt (k:=k) hz hF hp
  have hzD := (logPotential_critical_iff hk hz hF.differentiableAt hp).mpr hg
  have hsym : realHessian (logPotential k F ξ) z 1 I = realHessian (logPotential k F ξ) z I 1 := by
    rw [realHessian_eq_second (hl.of_le (by simp)),realHessian_eq_second (hl.of_le (by simp))]
    exact (hl.isSymmSndFDerivAt (by simp)).eq 1 I
  have hn := logPotential_hessian_det hk hz hF hd hg
  unfold Grid.hessianDet
  rw [← realHessian_eq_second hu,← realHessian_eq_second hu,← realHessian_eq_second hu]
  rw [squaredReciprocalPotential_hessian hz hF hp,squaredReciprocalPotential_hessian hz hF hp,
    squaredReciprocalPotential_hessian hz hF hp,hzD]
  simp only [zero_apply,mul_zero,zero_sub]
  rw [← hsym] at hn
  calc
    _ = 4*(squaredReciprocalPotential k F ξ z)^2 *
        (realHessian (logPotential k F ξ) z 1 1 * realHessian (logPotential k F ξ) z I I -
          realHessian (logPotential k F ξ) z 1 I * realHessian (logPotential k F ξ) z 1 I) := by ring
    _ = _ := by rw [hn]; ring

lemma squaredReciprocalPotential_hessian_det_pole {k : ℝ}
    {F : ℂ → ℂ} {ξ z : ℂ} (hz : 0<z.im) (hF : AnalyticAt ℂ F z)
    (hd : deriv F z≠0) (hp : F z=ξ) :
    0<Grid.hessianDet (squaredReciprocalPotential k F ξ) z := by
  have hu := (squaredReciprocalPotential_contDiffAt (k:=k) (ξ:=ξ) hz hF).of_le (show (2 : WithTop ℕ∞)≤⊤ by simp)
  unfold Grid.hessianDet
  rw [← realHessian_eq_second hu,← realHessian_eq_second hu,← realHessian_eq_second hu]
  rw [squaredReciprocalPotential_hessian_pole hz hF hp,squaredReciprocalPotential_hessian_pole hz hF hp,
    squaredReciprocalPotential_hessian_pole hz hF hp]
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  have hi : inner ℝ (deriv F z*1) (deriv F z*I)=0 := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
    simp only [mul_one]
    change (deriv F z * I * conj (deriv F z)).re = 0
    simp only [Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_sub]
    ring
  rw [hi]
  simp only [mul_zero,zero_mul,zero_pow (by norm_num : 2≠0),sub_zero]
  have hn : 0<‖deriv F z*1‖^2 := by simp [hd]
  have hn' : 0<‖deriv F z*I‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (mul_ne_zero hd I_ne_zero))
  have hy := Real.rpow_pos_of_pos hz (-2*k)
  positivity

end
end StrictInverseFirstPower

end

end OAI
