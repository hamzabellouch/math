import OAI.Geometry.PolarProducts.CanonicalCylinder

namespace OAI

universe u129 u130

section
namespace PlanarSquare
noncomputable section
open Set Filter
open scoped ContDiff Topology

def square : Set ℂ := {z | |z.re| < 1 ∧ |z.im| < 1}
def radius (z : ℂ) : ℝ := Real.sqrt (2*(z.im+1)/Real.pi)
def angle : ℂ →L[ℝ] ℂ := Complex.reCLM.smulRight (-(Real.pi : ℂ)*Complex.I)
def rotation (z : ℂ) : ℂ := Complex.exp (angle z)
def map (z : ℂ) : ℂ := (radius z : ℂ)*rotation z

theorem radius_pos {z : ℂ} (hz : -1 < z.im) : 0 < radius z := by
  apply Real.sqrt_pos.2
  exact div_pos (by linarith) Real.pi_pos

theorem radius_sq {z : ℂ} (hz : -1 < z.im) : radius z ^ 2 = 2*(z.im+1)/Real.pi :=
  Real.sq_sqrt (div_nonneg (by linarith) Real.pi_pos.le)

@[simp] theorem angle_re (z : ℂ) : (angle z).re = 0 := by simp [angle, Complex.mul_re, Complex.mul_im]
@[simp] theorem angle_im (z : ℂ) : (angle z).im = -Real.pi*z.re := by
  simp [angle, Complex.mul_re, Complex.mul_im, mul_comm]

@[simp] theorem norm_rotation (z : ℂ) : ‖rotation z‖ = 1 := by simp [rotation, Complex.norm_exp]

theorem norm_map_sq {z : ℂ} (hz : -1 < z.im) : ‖map z‖^2 = 2*(z.im+1)/Real.pi := by
  rw [map, norm_mul, norm_rotation, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, radius_sq hz]

theorem map_bound {z : ℂ} (hz : z ∈ square) : ‖map z‖^2 < 4/Real.pi := by
  rw [norm_map_sq (abs_lt.mp hz.2).1]
  exact (div_lt_div_iff_of_pos_right Real.pi_pos).2 (by linarith [(abs_lt.mp hz.2).2])

theorem map_injOn : InjOn map square := by
  intro z hz w hw hzw
  have him : z.im = w.im := by
    have hh := congrArg (fun t : ℂ => ‖t‖^2) hzw
    rw [norm_map_sq (abs_lt.mp hz.2).1, norm_map_sq (abs_lt.mp hw.2).1] at hh
    have := (div_left_inj' Real.pi_ne_zero).mp hh
    linarith
  have hrad : radius z = radius w := by simp only [radius, him]
  have hrot : rotation z = rotation w := by
    change (radius z : ℂ)*rotation z = (radius w : ℂ)*rotation w at hzw
    rw [← hrad] at hzw
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (radius_pos (abs_lt.mp hz.2).1).ne') hzw
  have hab (x : ℂ) (hx : x ∈ square) : -Real.pi < (angle x).im ∧ (angle x).im ≤ Real.pi := by
    rw [angle_im]
    have ht := mul_lt_mul_of_pos_left (abs_lt.mp hx.1).2 Real.pi_pos
    have hb := mul_lt_mul_of_pos_left (abs_lt.mp hx.1).1 Real.pi_pos
    constructor <;> linarith
  have hangle := Complex.exp_inj_of_neg_pi_lt_of_le_pi (hab z hz).1 (hab z hz).2
    (hab w hw).1 (hab w hw).2 hrot
  have hre : z.re = w.re := by
    have hh := congrArg Complex.im hangle
    simp only [angle_im] at hh
    nlinarith [Real.pi_pos]
  exact Complex.ext hre him

theorem contDiffAt_map {z : ℂ} (hz : -1 < z.im) : ContDiffAt ℝ ∞ map z := by
  have hrad : ContDiffAt ℝ ∞ radius z := by
    apply ContDiffAt.sqrt
    · exact (contDiffAt_const.mul (Complex.imCLM.contDiff.contDiffAt.add contDiffAt_const)).div_const Real.pi
    · exact ne_of_gt (div_pos (by linarith) Real.pi_pos)
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z hrad).mul (angle.contDiff.contDiffAt.cexp)

theorem hasFDerivAt_radius {z : ℂ} (hz : -1 < z.im) :
    HasFDerivAt radius ((1/(Real.pi*radius z)) • Complex.imCLM) z := by
  have hbase : HasFDerivAt (fun w : ℂ => 2*(w.im+1)/Real.pi)
      ((2/Real.pi) • Complex.imCLM) z := by
    have hf : (fun w : ℂ => 2*(w.im+1)/Real.pi) =
        (fun w : ℂ => (2/Real.pi)*(Complex.imCLM w+1)) := by funext w; simp only [Complex.imCLM_apply]; ring
    rw [hf]
    exact (Complex.imCLM.hasFDerivAt.add_const 1).const_mul (2/Real.pi)
  have hs := hbase.sqrt (ne_of_gt (div_pos (by linarith) Real.pi_pos))
  rw [smul_smul] at hs
  change HasFDerivAt radius (((1/(2*radius z))*(2/Real.pi)) • Complex.imCLM) z at hs
  have hcoef : (1/(2*radius z))*(2/Real.pi) = 1/(Real.pi*radius z) := by
    field_simp
  rwa [hcoef] at hs

def derivative (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (radius z : ℂ) • (rotation z • angle) +
    rotation z • (Complex.ofRealCLM.comp ((1/(Real.pi*radius z)) • Complex.imCLM))

theorem hasFDerivAt_map {z : ℂ} (hz : -1 < z.im) : HasFDerivAt map (derivative z) z := by
  exact ((Complex.ofRealCLM.hasFDerivAt.comp z (hasFDerivAt_radius hz)).mul
    angle.hasFDerivAt.cexp)

theorem derivative_apply (z v : ℂ) :
    derivative z v = rotation z * (((v.im/(Real.pi*radius z) : ℝ) : ℂ) -
      Complex.I * ((Real.pi*radius z*v.re : ℝ) : ℂ)) := by
  simp [derivative, angle, Complex.real_smul, smul_eq_mul, div_eq_mul_inv]
  ring

def form (v w : ℂ) : ℝ := v.re*w.im - w.re*v.im

theorem form_mul (a v w : ℂ) : form (a*v) (a*w) = ‖a‖^2*form v w := by
  simp only [form, Complex.mul_re, Complex.mul_im, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem derivative_preserves {z : ℂ} (hz : -1 < z.im) (v w : ℂ) :
    form (derivative z v) (derivative z w) = form v w := by
  simp only [derivative_apply, form_mul, norm_rotation, one_pow, one_mul]
  simp only [form, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hr := (radius_pos hz).ne'
  field_simp
  ring

end
end PlanarSquare
end

section
namespace PlanarCylinder
noncomputable section
open Set Filter
open scoped ContDiff Topology
variable {κ : Type u129} [Fintype κ] [DecidableEq κ]
abbrev V (κ : Type u130) := EuclideanSpace ℂ κ

def domain (j₀ : κ) : Set (V κ) := {z | z j₀ ∈ PlanarSquare.square}
def map (j₀ : κ) (z : V κ) : V κ :=
  (EuclideanSpace.equiv κ ℂ).symm (fun j => if j = j₀ then PlanarSquare.map (z j) else z j)

omit [Fintype κ] in
@[simp] theorem map_apply (j₀ j : κ) (z : V κ) :
    map j₀ z j = if j = j₀ then PlanarSquare.map (z j) else z j := rfl

omit [Fintype κ] in
@[simp] theorem map_first (j₀ : κ) (z : V κ) : map j₀ z j₀ = PlanarSquare.map (z j₀) := by simp

omit [Fintype κ] in
theorem map_injOn (j₀ : κ) : InjOn (map j₀) (domain j₀) := by
  intro z hz w hw hzw
  ext j
  have hh := congrArg (fun v : V κ => v j) hzw
  by_cases hj : j = j₀
  · subst j
    apply PlanarSquare.map_injOn hz hw
    simpa only [map_first] using hh
  · simpa only [map_apply, ite_eq_right hj] using hh

def derivative (j₀ : κ) (z : V κ) : V κ →L[ℝ] V κ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => if j = j₀ then
      (PlanarSquare.derivative (z j)).comp (PiLp.proj 2 (fun _ : κ => ℂ) j)
      else (PiLp.proj 2 (fun _ : κ => ℂ) j)))

omit [Fintype κ] in
@[simp] theorem derivative_apply (j₀ j : κ) (z v : V κ) :
    derivative j₀ z v j = if j = j₀ then PlanarSquare.derivative (z j) (v j) else v j := by
  change (if j = j₀ then (PlanarSquare.derivative (z j)).comp (PiLp.proj 2 (fun _ : κ => ℂ) j)
    else (PiLp.proj 2 (fun _ : κ => ℂ) j)) v = _
  split_ifs <;> rfl

theorem hasFDerivAt_map (j₀ : κ) {z : V κ} (hz : -1 < (z j₀).im) :
    HasFDerivAt (map j₀) (derivative j₀ z) z := by
  apply (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp
  apply hasFDerivAt_pi.mpr
  intro j
  by_cases hj : j = j₀
  · subst j
    simp only [ite_true]
    exact (PlanarSquare.hasFDerivAt_map hz).comp z (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 z j₀)
  · simp only [ite_eq_right hj]
    exact PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 z j

theorem contDiffAt_map (j₀ : κ) {z : V κ} (hz : -1 < (z j₀).im) :
    ContDiffAt ℝ ∞ (map j₀) z := by
  apply (contDiffAt_piLp 2).mpr
  intro j
  by_cases hj : j = j₀
  · subst j
    simp only [map_first]
    exact (PlanarSquare.contDiffAt_map hz).comp z
      (show ContDiffAt ℝ ∞ (fun w : V κ => w j₀) z from contDiffAt_piLp_apply 2)
  · simp only [map_apply, ite_eq_right hj]
    exact contDiffAt_piLp_apply 2

def form (v w : V κ) : ℝ := ∑ j, PlanarSquare.form (v j) (w j)

omit [DecidableEq κ] in
theorem form_eq_inner (v w : V κ) : form v w = inner (𝕜 := ℝ) (Complex.I • v) w := by
  simp only [form, PiLp.inner_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_eq_re_inner, RCLike.inner_apply']
  change PlanarSquare.form (v j) (w j) = ((starRingEnd ℂ) (Complex.I * v j) * w j).re
  simp only [PlanarSquare.form, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem derivative_preserves (j₀ : κ) {z : V κ} (hz : -1 < (z j₀).im) (v w : V κ) :
    form (derivative j₀ z v) (derivative j₀ z w) = form v w := by
  unfold form
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = j₀
  · subst j
    simp only [derivative_apply, ite_true]
    exact PlanarSquare.derivative_preserves hz _ _
  · simp only [derivative_apply, ite_eq_right hj]

omit [Fintype κ] in
theorem first_bound (j₀ : κ) {z : V κ} (hz : z ∈ domain j₀) :
    ‖map j₀ z j₀‖^2 < 4/Real.pi := by
  rw [map_first]
  exact PlanarSquare.map_bound hz

theorem norm_bound (j₀ : κ) {z : V κ} (hz : z ∈ domain j₀) :
    ‖map j₀ z‖^2 ≤ ‖z‖^2 + 4/Real.pi := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ j, (‖z j‖^2 + if j = j₀ then 4/Real.pi else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = j₀
      · subst j
        simp only [ite_true]
        exact (first_bound j₀ hz).le.trans (le_add_of_nonneg_left (sq_nonneg _))
      · simp [map_apply, ite_eq_right hj]
    _ = _ := by simp [Finset.sum_add_distrib]

end
end PlanarCylinder
end

end OAI
