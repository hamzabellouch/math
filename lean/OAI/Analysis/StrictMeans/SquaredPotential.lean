import OAI.Analysis.StrictMeans.IndexGeometry

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def squaredReciprocalPotential (k : ℝ) (F : ℂ → ℂ) (ξ z : ℂ) : ℝ :=
  ‖F z - ξ‖ ^ 2 * z.im ^ (-2*k)

lemma squaredReciprocalPotential_contDiffAt {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) :
    ContDiffAt ℝ ⊤ (squaredReciprocalPotential k F ξ) z := by
  exact (((hF.restrictScalars (𝕜 := ℝ)).contDiffAt.sub contDiffAt_const).norm_sq ℝ).mul
    (Complex.imCLM.contDiff.contDiffAt.rpow_const_of_ne hz.ne')

lemma squaredReciprocalPotential_eq_exp {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hp : F z ≠ ξ) :
    squaredReciprocalPotential k F ξ z = Real.exp (-2 * logPotential k F ξ z) := by
  have hn : 0 < ‖F z-ξ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
  unfold squaredReciprocalPotential logPotential
  rw [show -2*(k*Real.log z.im-Real.log ‖F z-ξ‖) =
      2*Real.log ‖F z-ξ‖ + Real.log z.im * (-2*k) by ring,
    Real.exp_add, ← Real.rpow_def_of_pos hz]
  congr 1
  rw [show 2*Real.log ‖F z-ξ‖ = Real.log (‖F z-ξ‖^2) by rw [Real.log_pow]; ring,
    Real.exp_log (sq_pos_of_pos hn)]

lemma logPotential_contDiffAt {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hp : F z ≠ ξ) :
    ContDiffAt ℝ ⊤ (logPotential k F ξ) z := by
  exact (contDiffAt_const.mul (Complex.imCLM.contDiff.contDiffAt.log hz.ne')).sub
    ((((hF.restrictScalars (𝕜 := ℝ)).contDiffAt.sub contDiffAt_const).norm ℝ
      (sub_ne_zero.mpr hp)).log (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp)))

lemma realHessian_exp {u : ℂ → ℝ} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) (v w : ℂ) :
    realHessian (fun t => Real.exp (u t)) z v w =
      Real.exp (u z) * (fderiv ℝ u z v * fderiv ℝ u z w + realHessian u z v w) := by
  have hdu := hu.differentiableAt (by norm_num)
  have huD : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hw : DifferentiableAt ℝ (fun t => fderiv ℝ u t w) z :=
    huD.clm_apply (differentiableAt_const w)
  have he : (fun t => fderiv ℝ (fun s => Real.exp (u s)) t w) =ᶠ[𝓝 z]
      (fun t => Real.exp (u t) * fderiv ℝ u t w) := by
    filter_upwards [hu.eventually (by norm_num)] with t ht
    rw [ht.differentiableAt (by norm_num) |>.hasFDerivAt.exp |>.fderiv]
    rfl
  unfold realHessian
  rw [he.fderiv_eq]
  change (fderiv ℝ ((fun t => Real.exp (u t)) * (fun t => fderiv ℝ u t w)) z) v = _
  rw [(hdu.hasFDerivAt.exp.mul hw.hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma squaredReciprocalPotential_hessian {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hp : F z ≠ ξ) (v w : ℂ) :
    realHessian (squaredReciprocalPotential k F ξ) z v w =
      squaredReciprocalPotential k F ξ z *
        (4 * fderiv ℝ (logPotential k F ξ) z v * fderiv ℝ (logPotential k F ξ) z w -
          2 * realHessian (logPotential k F ξ) z v w) := by
  have he : squaredReciprocalPotential k F ξ =ᶠ[𝓝 z]
      (fun t => Real.exp (-2 * logPotential k F ξ t)) := by
    filter_upwards [isOpen_halfPlane.mem_nhds hz,hF.continuousAt.eventually_ne hp] with t ht hpt
    exact squaredReciprocalPotential_eq_exp ht hpt
  have heH : realHessian (squaredReciprocalPotential k F ξ) z v w =
      realHessian (fun t => Real.exp (-2 * logPotential k F ξ t)) z v w := by
    unfold realHessian
    apply congrArg (fun L : ℂ →L[ℝ] ℝ => L v)
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [he.eventuallyEq_nhds] with t ht
    rw [ht.fderiv_eq]
  rw [heH,realHessian_exp ((contDiffAt_const.mul (logPotential_contDiffAt hz hF hp)).of_le (by norm_num)),
    ← squaredReciprocalPotential_eq_exp hz hp]
  have hd := logPotential_differentiableAt (k := k) hz hF.differentiableAt hp
  have hfirst : ∀ a : ℂ, fderiv ℝ (fun t => -2*logPotential k F ξ t) z a =
      -2*fderiv ℝ (logPotential k F ξ) z a := by
    intro a
    rw [(hd.hasFDerivAt.const_mul (-2)).fderiv]
    rfl
  have hsecond : realHessian (fun t => -2*logPotential k F ξ t) z v w =
      -2*realHessian (logPotential k F ξ) z v w := by
    have he' : (fun t => fderiv ℝ (fun s => -2*logPotential k F ξ s) t w) =ᶠ[𝓝 z]
        (fun t => -2 * fderiv ℝ (logPotential k F ξ) t w) := by
      filter_upwards [isOpen_halfPlane.mem_nhds hz,hF.eventually_analyticAt,
        hF.continuousAt.eventually_ne hp] with t ht hFt hpt
      rw [((logPotential_differentiableAt ht hFt.differentiableAt hpt).hasFDerivAt.const_mul (-2)).fderiv]
      rfl
    unfold realHessian
    rw [he'.fderiv_eq]
    have hw := ((logPotential_contDiffAt (k := k) hz hF hp).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    rw [(hw.clm_apply (differentiableAt_const w)).hasFDerivAt.const_mul (-2) |>.fderiv]
    rfl
  rw [hfirst,hfirst,hsecond]
  ring

lemma squaredReciprocalPotential_laplacian_pos_off_pole {k : ℝ} (hk : 0 < k)
    {F : ℂ → ℂ} {ξ z : ℂ} (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hp : F z ≠ ξ) :
    0 < planeLaplacian (squaredReciprocalPotential k F ξ) z := by
  change 0 < realHessian _ z 1 1 + realHessian _ z I I
  rw [squaredReciprocalPotential_hessian hz hF hp,squaredReciprocalPotential_hessian hz hF hp]
  have hu : 0 < squaredReciprocalPotential k F ξ z := by
    rw [squaredReciprocalPotential_eq_exp hz hp]
    exact Real.exp_pos _
  have ht := logPotential_hessian_trace (k := k) hz hF hp
  have hs : 0 < k/z.im^2 := div_pos hk (sq_pos_of_pos hz)
  calc
    _ = squaredReciprocalPotential k F ξ z *
        (4 * (fderiv ℝ (logPotential k F ξ) z 1)^2 +
         4 * (fderiv ℝ (logPotential k F ξ) z I)^2 + 2*(k/z.im^2)) := by
      rw [show k/z.im^2 = -(realHessian (logPotential k F ξ) z 1 1 +
        realHessian (logPotential k F ξ) z I I) by rw [ht]; ring]
      ring
    _ > 0 := mul_pos hu (by positivity)

lemma realHessian_mul {u t : ℂ → ℝ} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) (ht : ContDiffAt ℝ 2 t z) (v w : ℂ) :
    realHessian (fun a => u a * t a) z v w =
      realHessian u z v w * t z + fderiv ℝ u z w * fderiv ℝ t z v +
      fderiv ℝ u z v * fderiv ℝ t z w + u z * realHessian t z v w := by
  have hu1 := hu.differentiableAt (by norm_num)
  have ht1 := ht.differentiableAt (by norm_num)
  have hu2 := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have ht2 := (ht.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hwU := hu2.clm_apply (differentiableAt_const w)
  have hwT := ht2.clm_apply (differentiableAt_const w)
  have he : (fun a => fderiv ℝ (fun b => u b*t b) a w) =ᶠ[𝓝 z]
      (fun a => fderiv ℝ u a w * t a + u a * fderiv ℝ t a w) := by
    filter_upwards [hu.eventually (by norm_num),ht.eventually (by norm_num)] with a hUa hTa
    change fderiv ℝ (u*t) a w = _
    rw [((hUa.differentiableAt (by norm_num)).hasFDerivAt.mul
      (hTa.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring
  unfold realHessian
  rw [he.fderiv_eq]
  have hd := (hwU.hasFDerivAt.mul ht1.hasFDerivAt).add
    (hu1.hasFDerivAt.mul hwT.hasFDerivAt)
  change fderiv ℝ (((fun a => fderiv ℝ u a w) * t) +
    (u * (fun a => fderiv ℝ t a w))) z v = _
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

lemma realHessian_norm_sq_at_zero {F : ℂ → ℂ} {z : ℂ} (hF : ContDiffAt ℝ 2 F z)
    (hzero : F z = 0) (v w : ℂ) :
    realHessian (fun a => ‖F a‖^2) z v w =
      2 * inner ℝ (fderiv ℝ F z v) (fderiv ℝ F z w) := by
  have hd := hF.differentiableAt (by norm_num)
  have hd2 := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hw := hd2.clm_apply (differentiableAt_const w)
  have he : (fun a => fderiv ℝ (fun b => ‖F b‖^2) a w) =ᶠ[𝓝 z]
      (fun a => 2 * inner ℝ (F a) (fderiv ℝ F a w)) := by
    filter_upwards [hF.eventually (by norm_num)] with a ha
    rw [(ha.differentiableAt (by norm_num)).hasFDerivAt.norm_sq.fderiv]
    simp
    ring
  unfold realHessian
  rw [he.fderiv_eq]
  rw [((hd.hasFDerivAt.inner ℝ hw.hasFDerivAt).const_mul 2).fderiv]
  simp [hzero]

lemma squaredReciprocalPotential_fderiv_pole {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hp : F z = ξ) :
    fderiv ℝ (squaredReciprocalPotential k F ξ) z = 0 := by
  have hd := (hF.differentiableAt.restrictScalars (𝕜 := ℝ)).sub_const ξ
  have hy : DifferentiableAt ℝ (fun a : ℂ => a.im^(-2*k)) z :=
    (Complex.imCLM.contDiff.contDiffAt.rpow_const_of_ne (p := -2*k) hz.ne').differentiableAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  unfold squaredReciprocalPotential
  change fderiv ℝ ((fun a => ‖F a-ξ‖^2) * (fun a : ℂ => a.im^(-2*k))) z = 0
  rw [(hd.hasFDerivAt.norm_sq.mul hy.hasFDerivAt).fderiv]
  simp [hp]

lemma squaredReciprocalPotential_hessian_pole {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hp : F z = ξ) (v w : ℂ) :
    realHessian (squaredReciprocalPotential k F ξ) z v w =
      2 * inner ℝ (deriv F z * v) (deriv F z * w) * z.im^(-2*k) := by
  have hd : ContDiffAt ℝ 2 (fun a => F a-ξ) z :=
    (hF.restrictScalars (𝕜 := ℝ)).contDiffAt.sub contDiffAt_const
  have hy : ContDiffAt ℝ 2 (fun a : ℂ => a.im^(-2*k)) z :=
    Complex.imCLM.contDiff.contDiffAt.rpow_const_of_ne hz.ne'
  have hzF : F z-ξ = 0 := sub_eq_zero.mpr hp
  have hdn : fderiv ℝ (fun a => ‖F a-ξ‖^2) z = 0 := by
    rw [(hd.differentiableAt (by norm_num)).hasFDerivAt.norm_sq.fderiv]
    simp [hp]
  unfold squaredReciprocalPotential
  rw [realHessian_mul (hd.norm_sq ℝ) hy,hdn]
  simp only [zero_apply,zero_mul,add_zero,hzF,norm_zero,zero_pow (by norm_num : 2 ≠ 0)]
  rw [realHessian_norm_sq_at_zero hd hzF]
  have he : ∀ a : ℂ, fderiv ℝ (fun t => F t-ξ) z a = deriv F z * a := by
    intro a
    rw [((hF.differentiableAt.hasDerivAt.sub_const ξ).complexToReal_fderiv).fderiv]
    simp [mul_comm]
  rw [he,he]

lemma squaredReciprocalPotential_laplacian_pos {k : ℝ} (hk : 0 < k)
    {F : ℂ → ℂ} {ξ z : ℂ} (hz : 0 < z.im) (hF : AnalyticAt ℂ F z)
    (hd : deriv F z ≠ 0) :
    0 < planeLaplacian (squaredReciprocalPotential k F ξ) z := by
  by_cases hp : F z = ξ
  · change 0 < realHessian _ z 1 1 + realHessian _ z I I
    rw [squaredReciprocalPotential_hessian_pole hz hF hp,
      squaredReciprocalPotential_hessian_pole hz hF hp]
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
    have hpw := Real.rpow_pos_of_pos hz (-2*k)
    have hn : 0 < ‖deriv F z * 1‖^2 := by simp [hd]
    positivity
  · exact squaredReciprocalPotential_laplacian_pos_off_pole hk hz hF hp

end
end StrictInverseFirstPower

end

end OAI
