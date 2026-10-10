import OAI.Probability.SLE.Geometry.DiskQuarterGeometry

namespace OAI

/-! The elementary disk automorphism needed to compare derivatives on the
quarter disk. -/

noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge

def diskRecenter (w z : ℂ) : ℂ := (w+z)/(1+star w*z)

lemma diskRecenter_den_ne {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ < 1) :
    1+star w*z ≠ 0 := by
  intro h
  have hh : star w*z = -1 := by linear_combination h
  have hn := congrArg norm hh
  simp only [norm_mul,norm_star,norm_neg,norm_one] at hn
  nlinarith [norm_nonneg w,norm_nonneg z]

lemma diskRecenter_det {w : ℂ} (hw : ‖w‖ < 1) :
    1-star w*w = ((1-‖w‖^2:ℝ):ℂ) ∧ 0 < 1-‖w‖^2 := by
  constructor
  · simp only [Complex.star_def,Complex.conj_mul',Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow]
  · nlinarith [norm_nonneg w]

lemma diskRecenter_maps {w : ℂ} (hw : ‖w‖ < 1) :
    MapsTo (diskRecenter w) (ball 0 1) (ball 0 1) := by
  intro z hz
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hd := diskRecenter_den_ne hw hz'
  have hg : Complex.normSq (1+star w*z)-Complex.normSq (w+z) =
      (1-Complex.normSq w)*(1-Complex.normSq z) := by
    simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,
      Complex.mul_re,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
    ring
  have hp : 0 < (1-Complex.normSq w)*(1-Complex.normSq z) := by
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]
    exact mul_pos (diskRecenter_det hw).2 (diskRecenter_det hz').2
  rw [mem_ball_zero_iff,diskRecenter,norm_div]
  apply (div_lt_one (norm_pos_iff.mpr hd)).mpr
  simp only [Complex.normSq_eq_norm_sq] at hg hp
  nlinarith [norm_nonneg (w+z),norm_nonneg (1+star w*z)]

lemma diskRecenter_injOn {w : ℂ} (hw : ‖w‖ < 1) :
    InjOn (diskRecenter w) (ball 0 1) := by
  intro x hx y hy hxy
  have hx' := diskRecenter_den_ne hw (mem_ball_zero_iff.mp hx)
  have hy' := diskRecenter_den_ne hw (mem_ball_zero_iff.mp hy)
  have hh := (div_eq_div_iff hx' hy').mp hxy
  have he : (1-star w*w)*(x-y)=0 := by linear_combination hh
  have hn : 1-star w*w ≠ 0 := by
    rw [(diskRecenter_det hw).1]
    exact_mod_cast (diskRecenter_det hw).2.ne'
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hn)

lemma diskRecenter_hasDerivAt {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (diskRecenter w) ((1-star w*w)/(1+star w*z)^2) z := by
  have hh := ((hasDerivAt_id z).const_add w).div
    (((hasDerivAt_id z).const_mul (star w)).const_add 1) (diskRecenter_den_ne hw hz)
  convert hh using 1 <;> first | rfl | (dsimp; ring)

lemma diskRecenter_differentiable {w : ℂ} (hw : ‖w‖ < 1) :
    DifferentiableOn ℂ (diskRecenter w) (ball 0 1) := by
  intro z hz
  exact (diskRecenter_hasDerivAt hw (mem_ball_zero_iff.mp hz)).differentiableAt.differentiableWithinAt

@[simp] lemma diskRecenter_zero (w : ℂ) : diskRecenter w 0=w := by simp [diskRecenter]
@[simp] lemma diskRecenter_neg (w : ℂ) : diskRecenter w (-w)=0 := by simp [diskRecenter]

lemma diskRecenter_deriv_zero {w : ℂ} (hw : ‖w‖ < 1) :
    ‖deriv (diskRecenter w) 0‖=1-‖w‖^2 := by
  rw [(diskRecenter_hasDerivAt hw (by simp)).deriv]
  simp only [mul_zero,add_zero,one_pow,div_one,(diskRecenter_det hw).1]
  exact Complex.norm_of_nonneg (diskRecenter_det hw).2.le

lemma diskRecenter_deriv_neg {w : ℂ} (hw : ‖w‖ < 1) :
    ‖deriv (diskRecenter w) (-w)‖=(1-‖w‖^2)⁻¹ := by
  have hz : ‖-w‖ < 1 := by simpa only [norm_neg] using hw
  rw [(diskRecenter_hasDerivAt hw hz).deriv]
  have he : 1+star w*(-w)=1-star w*w := by ring
  rw [he]
  have hn : 1-star w*w ≠ 0 := by
    rw [(diskRecenter_det hw).1]
    exact_mod_cast (diskRecenter_det hw).2.ne'
  have hquot : (1-star w*w)/(1-star w*w)^2=(1-star w*w)⁻¹ := by
    field_simp [hn]
  rw [hquot]
  simp only [norm_inv,(diskRecenter_det hw).1,
    Complex.norm_of_nonneg (diskRecenter_det hw).2.le]

end SLEExactGauge

end

end OAI
