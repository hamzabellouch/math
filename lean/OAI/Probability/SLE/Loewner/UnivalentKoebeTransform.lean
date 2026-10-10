import OAI.Probability.SLE.Geometry.DiskRecentering
import OAI.Probability.SLE.Loewner.UnivalentOddRoot

namespace OAI

/-! The exact second-derivative calculation for disk recentering.
A bound on the second coefficient of normalized univalent functions
therefore controls their logarithmic derivative throughout the disk. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma diskRecenter_second_deriv_zero {a : ℂ} (ha : ‖a‖<1) :
    HasDerivAt (deriv (diskRecenter a)) (-2*star a*(1-star a*a)) 0 := by
  let D (z : ℂ) := (1-star a*a)/(1+star a*z)^2
  have hd : HasDerivAt D (-2*star a*(1-star a*a)) 0 := by
    have hh := (hasDerivAt_const (0:ℂ) (1-star a*a)).div
      ((((hasDerivAt_id (0:ℂ)).const_mul (star a)).const_add 1).pow 2)
      (by simp : (1+star a*(0:ℂ))^2≠0)
    change HasDerivAt D _ 0 at hh
    convert hh using 1
    simp
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [ball_mem_nhds (0:ℂ) zero_lt_one] with z hz
  exact (diskRecenter_hasDerivAt ha (mem_ball_zero_iff.mp hz)).deriv

lemma deriv_comp_diskRecenter_zero {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) {a : ℂ} (ha : ‖a‖<1) :
    deriv (f ∘ diskRecenter a) 0=deriv f a*(1-star a*a) := by
  have hfa := hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ha))
  have hfa' : HasDerivAt f (deriv f a) (diskRecenter a 0) := by simpa using hfa.hasDerivAt
  have hd := hfa'.comp 0 (diskRecenter_hasDerivAt ha (by simp))
  simpa using hd.deriv

lemma second_deriv_comp_diskRecenter_zero {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) {a : ℂ} (ha : ‖a‖<1) :
    deriv (deriv (f ∘ diskRecenter a)) 0 =
      deriv (deriv f) a*(1-star a*a)^2-2*star a*deriv f a*(1-star a*a) := by
  have hfa := hf.analyticAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ha))
  have hDfa : HasDerivAt (deriv f) (deriv (deriv f) a) (diskRecenter a 0) := by
    simpa using hfa.deriv.differentiableAt.hasDerivAt
  have hφ := diskRecenter_hasDerivAt ha (by simp : ‖(0:ℂ)‖<1)
  have hleft : HasDerivAt (deriv f ∘ diskRecenter a)
      (deriv (deriv f) a*(1-star a*a)) 0 := by
    simpa using hDfa.comp 0 hφ
  have hprod := hleft.mul (diskRecenter_second_deriv_zero ha)
  have hg : HasDerivAt (deriv (f ∘ diskRecenter a))
      (deriv (deriv f) a*(1-star a*a)*deriv (diskRecenter a) 0+
       deriv f (diskRecenter a 0)*(-2*star a*(1-star a*a))) 0 := by
    apply hprod.congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds (0:ℂ) zero_lt_one] with z hz
    exact (deriv_comp z (hf.differentiableAt (isOpen_ball.mem_nhds (diskRecenter_maps ha hz)))
      (diskRecenter_hasDerivAt ha (mem_ball_zero_iff.mp hz)).differentiableAt)
  rw [hg.deriv]
  rw [(diskRecenter_hasDerivAt ha (by simp : ‖(0:ℂ)‖<1)).deriv]
  simp only [diskRecenter_zero,mul_zero,add_zero,one_pow,div_one]
  ring

lemma univalent_preSchwarzian_of_second_derivative
    (hsecond : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 1) →
      InjOn f (ball 0 1) → ‖deriv (deriv f) 0‖≤4*‖deriv f 0‖)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hi : InjOn f (ball 0 1)) {a : ℂ} (ha : ‖a‖<1) :
    ‖((1-‖a‖^2:ℝ):ℂ)*deriv (deriv f) a/deriv f a-2*star a‖≤4 := by
  let d : ℝ := 1-‖a‖^2
  have hd : 0<d := (diskRecenter_det ha).2
  have hfa : deriv f a≠0 := univalent_deriv_ne_zero isOpen_ball hf hi (mem_ball_zero_iff.mpr ha)
  have hpos : 0<d*‖deriv f a‖ := mul_pos hd (norm_pos_iff.mpr hfa)
  have hb := hsecond (f ∘ diskRecenter a)
    (hf.comp (diskRecenter_differentiable ha) (diskRecenter_maps ha))
    (hi.comp (diskRecenter_injOn ha) (diskRecenter_maps ha))
  rw [second_deriv_comp_diskRecenter_zero hf ha,deriv_comp_diskRecenter_zero hf ha,
    (diskRecenter_det ha).1] at hb
  have he : deriv (deriv f) a*(d:ℂ)^2-2*star a*deriv f a*(d:ℂ)=
      ((d:ℂ)*deriv f a)*((d:ℂ)*deriv (deriv f) a/deriv f a-2*star a) := by
    field_simp
  change ‖deriv (deriv f) a*(d:ℂ)^2-2*star a*deriv f a*(d:ℂ)‖≤4*‖deriv f a*(d:ℂ)‖ at hb
  rw [he,norm_mul,norm_mul,norm_mul,Complex.norm_of_nonneg hd.le] at hb
  apply (mul_le_mul_iff_right₀ hpos).mp
  nlinarith [hb]

end SLEExactGauge

end

end OAI
