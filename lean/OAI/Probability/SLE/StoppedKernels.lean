import Mathlib
import OAI.Probability.SLE.AngularLaws
import OAI.Probability.SLE.DiskHalfPlane

namespace OAI

/-! Stopped Kernels for chordal SLE. -/

section
section
section
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian RealInnerProductSpace
namespace SLEExactGauge
lemma diskLogRadius_laplacian {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) :
    (Δ (diskLogRadius f)) z = -4 / diskWeight z ^ 2 := by
  have hh := (((hd.deriv isOpen_ball).analyticAt (isOpen_ball.mem_nhds hz))).harmonicAt_log_norm hne
  have he := hh.2.eq_of_nhds
  change (Δ (fun w => Real.log ‖deriv f w‖)) z = 0 at he
  rw [show diskLogRadius f = (fun w => Real.log (diskWeight w)) +
      (fun w => Real.log ‖deriv f w‖) from rfl,
    (diskWeight_contDiff.contDiffAt.log (diskWeight_pos hz).ne').laplacian_add hh.1,
    he, add_zero, log_diskWeight_laplacian hz]

lemma diskLogRadius_exp {f : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) :
    Real.exp (diskLogRadius f z) = diskWeight z * ‖deriv f z‖ := by
  simp only [diskLogRadius, Real.exp_add, Real.exp_log (diskWeight_pos hz),
    Real.exp_log (norm_pos_iff.mpr hne)]

lemma log_diskWeight_direction_bound {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (v : ℂ) :
    diskWeight z * |fderiv ℝ (fun w => Real.log (diskWeight w)) z v| ≤ 2 * ‖v‖ := by
  have hh := ((diskWeight_contDiff.differentiable (by norm_num) z).hasFDerivAt.log
    (diskWeight_pos hz).ne').fderiv
  rw [hh, diskWeight_fderiv]
  simp only [smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos (diskWeight_pos hz),
    abs_neg, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  rw [← mul_assoc, mul_inv_cancel₀ (diskWeight_pos hz).ne', one_mul]
  have hinner := abs_real_inner_le_norm z v
  have hn : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
  change 2 * |inner ℝ z v| ≤ 2 * ‖v‖
  calc
    _ ≤ 2 * (‖z‖ * ‖v‖) := mul_le_mul_of_nonneg_left hinner (by norm_num)
    _ ≤ 2 * ‖v‖ := by nlinarith [norm_nonneg v]

lemma disk_preSchwarzian_weight {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) :
    diskWeight z * ‖deriv (deriv f) z / deriv f z‖ ≤ 2560 * Real.pi + 4 := by
  have hh := disk_preSchwarzian_bound hd hi hg hgf hz hne
  have hb := norm_add_le
    (((diskWeight z : ℝ) : ℂ) * (deriv (deriv f) z / deriv f z) - 2 * star z) (2 * star z)
  rw [sub_add_cancel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (diskWeight_pos hz)] at hb
  have he : ‖(2 : ℂ) * star z‖ = 2 * ‖z‖ := by simp
  rw [he] at hb
  have hn := mem_ball_zero_iff.mp hz
  change ‖((diskWeight z : ℝ) : ℂ) * (deriv (deriv f) z / deriv f z) - 2 * star z‖ ≤ _ at hh
  linarith

lemma diskLogRadius_direction_bound {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) (v : ℂ) :
    diskWeight z * |fderiv ℝ (diskLogRadius f) z v| ≤ (2560 * Real.pi + 6) * ‖v‖ := by
  have hdd := ((hd.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hz))
  have hn : DifferentiableAt ℝ (fun w => Real.log ‖deriv f w‖) z :=
    ((hdd.restrictScalars ℝ).norm ℂ hne).log (norm_ne_zero_iff.mpr hne)
  have hw : DifferentiableAt ℝ (fun w => Real.log (diskWeight w)) z :=
    (diskWeight_contDiff.differentiable (by norm_num) z).log (diskWeight_pos hz).ne'
  have hp := disk_preSchwarzian_weight hd hi hg hgf hz hne
  have h1 := log_diskWeight_direction_bound hz v
  have h2 := log_norm_direction_bound hdd hne v
  have he : fderiv ℝ (diskLogRadius f) z =
      fderiv ℝ (fun w => Real.log (diskWeight w)) z +
        fderiv ℝ (fun w => Real.log ‖deriv f w‖) z := by
    exact fderiv_fun_add hw hn
  rw [he, add_apply]
  have hb := mul_le_mul_of_nonneg_left (abs_add_le
    (fderiv ℝ (fun w => Real.log (diskWeight w)) z v)
    (fderiv ℝ (fun w => Real.log ‖deriv f w‖) z v)) (diskWeight_pos hz).le
  have hb2 := mul_le_mul_of_nonneg_left h2 (diskWeight_pos hz).le
  have hb3 := mul_le_mul_of_nonneg_right hp (norm_nonneg v)
  nlinarith

lemma diskLogRadius_gradient_bound {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) :
    diskWeight z ^ 2 * ((fderiv ℝ (diskLogRadius f) z 1) ^ 2 +
      (fderiv ℝ (diskLogRadius f) z I) ^ 2) ≤ 2 * (2560 * Real.pi + 6) ^ 2 := by
  have h1 := diskLogRadius_direction_bound hd hi hg hgf hz hne 1
  have hI := diskLogRadius_direction_bound hd hi hg hgf hz hne I
  simp only [norm_one, norm_I, mul_one] at h1 hI
  have hw := (diskWeight_pos hz).le
  have hc : 0 ≤ 2560 * Real.pi + 6 := by positivity
  have h1' := sq_le_sq₀ (mul_nonneg hw (abs_nonneg _)) hc |>.mpr h1
  have hI' := sq_le_sq₀ (mul_nonneg hw (abs_nonneg _)) hc |>.mpr hI
  simp only [mul_pow, sq_abs] at h1' hI'
  nlinarith

end SLEExactGauge

end

 
section

open Set Filter Metric
open scoped Topology
namespace SLEExactGauge

 

noncomputable def layerProfile (r q x : ℝ) : ℝ :=
  r ^ 2 * Real.exp (q * (x - Real.log r)) / (1 + Real.exp (q * (x - Real.log r)))

noncomputable def layerProfileDeriv (r q x : ℝ) : ℝ :=
  q * r ^ 2 * Real.exp (q * (x - Real.log r)) /
    (1 + Real.exp (q * (x - Real.log r))) ^ 2

lemma layerProfile_hasDeriv (r q x : ℝ) :
    HasDerivAt (layerProfile r q) (layerProfileDeriv r q x) x := by
  have ht := (((hasDerivAt_id x).sub_const (Real.log r)).const_mul q).exp
  have hp := ((ht.const_mul (r ^ 2)).div (ht.const_add 1)
    (by positivity : 1 + Real.exp (q * (x - Real.log r)) ≠ 0))
  have hne : 1 + Real.exp (q * (x - Real.log r)) ≠ 0 := by positivity
  convert! hp using 1
  simp only [layerProfileDeriv, id_eq, mul_one]
  field_simp [hne]
  ring

lemma layerProfileDeriv_hasDeriv (r q x : ℝ) :
    HasDerivAt (layerProfileDeriv r q)
      (q * layerProfileDeriv r q x *
        ((1 - Real.exp (q * (x - Real.log r))) /
          (1 + Real.exp (q * (x - Real.log r))))) x := by
  have ht := (((hasDerivAt_id x).sub_const (Real.log r)).const_mul q).exp
  have hp := ((ht.const_mul (q * r ^ 2)).div ((ht.const_add 1).pow 2)
    (by positivity : (1 + Real.exp (q * (x - Real.log r))) ^ 2 ≠ 0))
  have hne : 1 + Real.exp (q * (x - Real.log r)) ≠ 0 := by positivity
  convert! hp using 1
  simp only [layerProfileDeriv, id_eq, Pi.pow_apply, mul_one,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [hne]
  ring

lemma layerProfile_contDiff (r q : ℝ) : ContDiff ℝ 2 (layerProfile r q) := by
  unfold layerProfile
  fun_prop (disch := intros; positivity)

lemma layerProfile_nonneg (r q x : ℝ) : 0 ≤ layerProfile r q x := by
  unfold layerProfile
  positivity

lemma layerProfile_le (r q x : ℝ) : layerProfile r q x ≤ r ^ 2 := by
  unfold layerProfile
  apply (div_le_iff₀ (by positivity)).mpr
  have ht := Real.exp_pos (q * (x - Real.log r))
  nlinarith [sq_nonneg r]

lemma layerProfile_deriv_nonneg {r q x : ℝ} (hq : 0 ≤ q) :
    0 ≤ deriv (layerProfile r q) x := by
  rw [(layerProfile_hasDeriv r q x).deriv]
  unfold layerProfileDeriv
  positivity

lemma layerProfile_second_le {r q x : ℝ} (hq : 0 ≤ q) :
    deriv (deriv (layerProfile r q)) x ≤ q * deriv (layerProfile r q) x := by
  have he : deriv (layerProfile r q) = layerProfileDeriv r q :=
    funext fun x => (layerProfile_hasDeriv r q x).deriv
  rw [he, (layerProfileDeriv_hasDeriv r q x).deriv]
  have ht : 0 < Real.exp (q * (x - Real.log r)) := Real.exp_pos _
  have hratio : (1 - Real.exp (q * (x - Real.log r))) /
      (1 + Real.exp (q * (x - Real.log r))) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hd : 0 ≤ layerProfileDeriv r q x := by unfold layerProfileDeriv; positivity
  simpa using mul_le_mul_of_nonneg_left hratio (mul_nonneg hq hd)

lemma layerProfile_deriv_lower {r q x : ℝ}
    (hr : 0 < r) (hq : 0 ≤ q) (hq2 : q ≤ 2) (hx : x ≤ Real.log r) :
    q / 4 * Real.exp x ^ 2 ≤ deriv (layerProfile r q) x := by
  rw [(layerProfile_hasDeriv r q x).deriv]
  let t := Real.exp (q * (x - Real.log r))
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos hq (sub_nonpos.mpr hx)
  have hlow : Real.exp (2 * (x - Real.log r)) ≤ t := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_right hq2 (sub_nonpos.mpr hx)
  have he : Real.exp x ^ 2 = r ^ 2 * Real.exp (2 * (x - Real.log r)) := by
    have h2 (y : ℝ) : Real.exp (2 * y) = Real.exp y ^ 2 := by simpa using Real.exp_nat_mul y 2
    rw [mul_sub, Real.exp_sub, h2, h2, Real.exp_log hr]
    field_simp [hr.ne']
  have he' : Real.exp x ^ 2 ≤ r ^ 2 * t := by rw [he]; exact mul_le_mul_of_nonneg_left hlow (sq_nonneg r)
  change q / 4 * Real.exp x ^ 2 ≤ q * r ^ 2 * t / (1 + t) ^ 2
  apply (le_div_iff₀ (by positivity)).mpr
  have hden : (1 + t) ^ 2 ≤ 4 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hden (mul_nonneg (div_nonneg hq (by norm_num : (0 : ℝ) ≤ 4)) (sq_nonneg (Real.exp x)))
  have hh' := mul_le_mul_of_nonneg_left he' hq
  nlinarith

end SLEExactGauge

end

 
section

open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
namespace SLEExactGauge

noncomputable def layerExponent : ℝ := (2 * (2560 * Real.pi + 6) ^ 2 + 1)⁻¹

lemma layerExponent_pos : 0 < layerExponent := by unfold layerExponent; positivity
lemma layerExponent_le_one : layerExponent ≤ 1 := by
  unfold layerExponent
  apply (inv_le_one₀ (by positivity)).mpr
  nlinarith [sq_nonneg (2560 * Real.pi + 6)]
lemma layerExponent_gradient : layerExponent * (2 * (2560 * Real.pi + 6) ^ 2) ≤ 1 := by
  unfold layerExponent
  have hp : 0 < 2 * (2560 * Real.pi + 6) ^ 2 + 1 := by positivity
  have he := inv_mul_cancel₀ hp.ne'
  have hn : 0 ≤ (2 * (2560 * Real.pi + 6) ^ 2 + 1)⁻¹ := by positivity
  nlinarith

noncomputable def diskLayerBarrier (f : ℂ → ℂ) (r : ℝ) : ℂ → ℝ :=
  layerProfile r layerExponent ∘ diskLogRadius f

lemma diskLayerBarrier_bounds (f : ℂ → ℂ) (r : ℝ) (z : ℂ) :
    0 ≤ diskLayerBarrier f r z ∧ diskLayerBarrier f r z ≤ r ^ 2 :=
  ⟨layerProfile_nonneg _ _ _, layerProfile_le _ _ _⟩

lemma diskLayerBarrier_contDiffAt {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) (r : ℝ) :
    ContDiffAt ℝ 2 (diskLayerBarrier f r) z :=
  (layerProfile_contDiff r layerExponent).contDiffAt.comp z (diskLogRadius_contDiffAt hd hz hne)

lemma diskLayerBarrier_laplacian_le {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) (r : ℝ) :
    (Δ (diskLayerBarrier f r)) z ≤
      -3 * deriv (layerProfile r layerExponent) (diskLogRadius f z) / diskWeight z ^ 2 := by
  let b := deriv (layerProfile r layerExponent) (diskLogRadius f z)
  let c := deriv (deriv (layerProfile r layerExponent)) (diskLogRadius f z)
  let S := (fderiv ℝ (diskLogRadius f) z 1) ^ 2 + (fderiv ℝ (diskLogRadius f) z I) ^ 2
  have hb : 0 ≤ b := layerProfile_deriv_nonneg layerExponent_pos.le
  have hc : c ≤ layerExponent * b := layerProfile_second_le layerExponent_pos.le
  have hS : 0 ≤ S := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hgrad := diskLogRadius_gradient_bound hd hi hg hgf hz hne
  change diskWeight z ^ 2 * S ≤ 2 * (2560 * Real.pi + 6) ^ 2 at hgrad
  have hterm : c * (diskWeight z ^ 2 * S) ≤ b := calc
    _ ≤ (layerExponent * b) * (diskWeight z ^ 2 * S) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg _) hS)
    _ ≤ (layerExponent * b) * (2 * (2560 * Real.pi + 6) ^ 2) :=
      mul_le_mul_of_nonneg_left hgrad (mul_nonneg layerExponent_pos.le hb)
    _ = b * (layerExponent * (2 * (2560 * Real.pi + 6) ^ 2)) := by ring
    _ ≤ b * 1 := mul_le_mul_of_nonneg_left layerExponent_gradient hb
    _ = b := mul_one b
  have hh := plane_laplacian_chain (diskLogRadius_contDiffAt hd hz hne)
    ((layerProfile_contDiff r layerExponent).contDiffAt)
  rw [diskLogRadius_laplacian hd hz hne] at hh
  change (Δ (diskLayerBarrier f r)) z = b * (-4 / diskWeight z ^ 2) + c * S at hh
  rw [hh]
  change b * (-4 / diskWeight z ^ 2) + c * S ≤ -3 * b / diskWeight z ^ 2
  have hw : 0 < diskWeight z ^ 2 := sq_pos_of_pos (diskWeight_pos hz)
  apply (le_div_iff₀ hw).mpr
  field_simp [(diskWeight_pos hz).ne']
  nlinarith [hterm]

lemma diskLayerBarrier_superharmonic {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) (r : ℝ) :
    (Δ (diskLayerBarrier f r)) z ≤ 0 := by
  apply (diskLayerBarrier_laplacian_le hd hi hg hgf hz hne r).trans
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (layerProfile_deriv_nonneg layerExponent_pos.le))
    (sq_nonneg _)

lemma diskLayerBarrier_layer_lower {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0)
    {r : ℝ} (hr : 0 < r) (hsmall : diskWeight z * ‖deriv f z‖ ≤ r) :
    layerExponent / 4 * ‖deriv f z‖ ^ 2 ≤ -(Δ (diskLayerBarrier f r)) z := by
  have hx : diskLogRadius f z ≤ Real.log r := by
    apply Real.exp_le_exp.mp
    rw [diskLogRadius_exp hz hne, Real.exp_log hr]
    exact hsmall
  have hlow := layerProfile_deriv_lower hr layerExponent_pos.le
    (layerExponent_le_one.trans (by norm_num : (1 : ℝ) ≤ 2)) hx
  rw [diskLogRadius_exp hz hne, mul_pow] at hlow
  have hh := diskLayerBarrier_laplacian_le hd hi hg hgf hz hne r
  have hb := layerProfile_deriv_nonneg (r := r) (x := diskLogRadius f z) layerExponent_pos.le
  have hw : 0 < diskWeight z ^ 2 := sq_pos_of_pos (diskWeight_pos hz)
  have hh' := (le_div_iff₀ hw).mp hh
  apply (mul_le_mul_iff_right₀ hw).mp
  nlinarith [hlow, hh']

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology Laplacian ENNReal
namespace SLEExactGauge

lemma conformal_layer_measurable {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (r : ℝ) :
    MeasurableSet {z | z ∈ ball (0 : ℂ) 1 ∧ diskWeight z * ‖deriv f z‖ ≤ r} := by
  have hcont : ContinuousOn (fun z => diskWeight z * ‖deriv f z‖) (ball (0 : ℂ) 1) :=
    diskWeight_contDiff.continuous.continuousOn.mul (hd.deriv isOpen_ball).continuousOn.norm
  rcases continuousOn_iff_isClosed.mp hcont (Iic r) isClosed_Iic with ⟨K, hK, heK⟩
  change MeasurableSet (ball (0 : ℂ) 1 ∩ (fun z => diskWeight z * ‖deriv f z‖) ⁻¹' Iic r)
  rw [inter_comm, heK]
  exact hK.measurableSet.inter measurableSet_ball

lemma disk_conformal_layer_green_le {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    (hne : ∀ w ∈ ball (0 : ℂ) 1, deriv f w ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ z in {z | z ∈ ball (0 : ℂ) 1 ∧ diskWeight z * ‖deriv f z‖ ≤ r},
      ENNReal.ofReal ((-Real.log ‖z‖) * ‖deriv f z‖ ^ 2)) ≤
      ENNReal.ofReal ((8 * Real.pi / layerExponent) * r ^ 2) := by
  let S := {z | z ∈ ball (0 : ℂ) 1 ∧ diskWeight z * ‖deriv f z‖ ≤ r}
  let V := diskLayerBarrier f r
  have hV := disk_green_le (fun z hz => diskLayerBarrier_contDiffAt hd hz (hne z hz) r)
    (fun z _ => (diskLayerBarrier_bounds f r z).1)
    (fun z _ => (diskLayerBarrier_bounds f r z).2)
    (fun z hz => diskLayerBarrier_superharmonic hd hi hg hgf hz (hne z hz) r)
  have hS : MeasurableSet S := conformal_layer_measurable hd r
  have hc : 0 ≤ (4 : ℝ) / layerExponent := div_nonneg (by norm_num) layerExponent_pos.le
  calc
    _ ≤ ∫⁻ z in S, ENNReal.ofReal ((4 / layerExponent) *
        ((-Real.log ‖z‖) * (-(Δ V) z))) := by
      apply setLIntegral_mono' hS
      intro z hz
      apply ENNReal.ofReal_le_ofReal
      have hl := diskLayerBarrier_layer_lower hd hi hg hgf hz.1 (hne z hz.1) hr hz.2
      have h'd : ‖deriv f z‖ ^ 2 ≤ 4 / layerExponent * (-(Δ V) z) := by
        have he : (4 / layerExponent) * (layerExponent / 4 * ‖deriv f z‖ ^ 2) =
            ‖deriv f z‖ ^ 2 := by field_simp [layerExponent_pos.ne']
        rw [← he]
        exact mul_le_mul_of_nonneg_left hl hc
      have hlog : 0 ≤ -Real.log ‖z‖ := neg_nonneg.mpr
        (Real.log_nonpos (norm_nonneg z) (mem_ball_zero_iff.mp hz.1).le)
      nlinarith [mul_le_mul_of_nonneg_left h'd hlog]
    _ ≤ ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal ((4 / layerExponent) *
        ((-Real.log ‖z‖) * (-(Δ V) z))) :=
      lintegral_mono_set (fun z hz => hz.1)
    _ = ENNReal.ofReal (4 / layerExponent) *
        ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal ((-Real.log ‖z‖) * (-(Δ V) z)) := by
      simp only [ENNReal.ofReal_mul hc]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (4 / layerExponent) * ENNReal.ofReal (2 * Real.pi * r ^ 2) :=
      mul_le_mul_right hV _
    _ = _ := by rw [← ENNReal.ofReal_mul hc]; congr 1; ring

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge

lemma complex_derivative_det (c : ℂ) :
    (((1 : ℂ →L[ℂ] ℂ).smulRight c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
    Complex.normSq_eq_norm_sq]

lemma conformal_disk_area_change {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (H : ℂ → ℝ≥0∞) :
    (∫⁻ w in f '' ball (0 : ℂ) 1, H w) =
      ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv f z‖ ^ 2) * H (f z) := by
  have hf (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      HasFDerivWithinAt f (((1 : ℂ →L[ℂ] ℂ).smulRight (deriv f z)).restrictScalars ℝ)
        (ball (0 : ℂ) 1) z :=
    ((hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hh := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball hf hi H
  simpa only [complex_derivative_det, abs_pow, abs_norm] using hh

lemma chart_deriv_ne_zero {D : Set ℂ} {f g : ℂ → ℂ}
    (hD : IsOpen D) (hd : DifferentiableOn ℂ f (ball 0 1))
    (hg : DifferentiableOn ℂ g D) (hm : MapsTo f (ball 0 1) D)
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : deriv f z ≠ 0 := by
  have hfz := (hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hgz := (hg.differentiableAt (hD.mem_nhds (hm hz))).hasDerivAt
  have heq : (g ∘ f) =ᶠ[𝓝 z] id := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hgf w hw
  have he : deriv g (f z) * deriv f z = 1 :=
    ((hgz.comp z hfz).congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id z)
  intro hn
  simp only [hn, mul_zero, zero_ne_one] at he

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology
namespace SLEExactGauge

 

lemma disk_radius_le_frontier_distance {D : Set ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hfront : (frontier D).Nonempty)
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hImage : f '' ball (0 : ℂ) 1 = D) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    diskWeight z * ‖deriv f z‖ ≤ (256 * Real.pi) * infDist (f z) (frontier D) := by
  have hc : 0 < 256 * Real.pi := by positivity
  have hr : 0 < 1 - ‖z‖ := sub_pos.mpr (mem_ball_zero_iff.mp hz)
  have hsub : ball z (1 - ‖z‖) ⊆ ball (0 : ℂ) 1 :=
    ball_subset_ball' (by simp only [dist_zero_right]; linarith)
  have hh : diskWeight z * ‖deriv f z‖ / (256 * Real.pi) ≤ infDist (f z) (frontier D) := by
    apply (le_infDist hfront).mpr
    intro a ha
    have hnot : a ∉ f '' ball z (1 - ‖z‖) := by
      intro hm
      have hIn : a ∈ D := hImage ▸ image_mono hsub hm
      exact ha.2 (by simpa only [hD.interior_eq] using hIn)
    have hk := univalent_omitted_value_bound_ball hr (hd.mono hsub) (hi.mono hsub) a hnot
    apply (div_le_iff₀ hc).mpr
    rw [dist_eq_norm]
    unfold diskWeight
    have hn := mul_nonneg (sq_nonneg (1 - ‖z‖)) (norm_nonneg (deriv f z))
    nlinarith [hk, hn]
  have hb := (div_le_iff₀ hc).mp hh
  simpa only [mul_comm] using hb

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge

noncomputable def layerGreenConstant : ℝ :=
  (8 * Real.pi / layerExponent) * (256 * Real.pi) ^ 2

lemma layerGreenConstant_pos : 0 < layerGreenConstant := by
  unfold layerGreenConstant
  exact mul_pos (div_pos (by positivity) layerExponent_pos) (sq_pos_of_pos (by positivity))

lemma centered_boundary_layer_green_le {D : Set ℂ} {f g : ℂ → ℂ}
    (hD : IsOpen D) (hfront : (frontier D).Nonempty)
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hg : DifferentiableOn ℂ g D)
    (hmf : MapsTo f (ball 0 1) D) (hmg : MapsTo g D (ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    (hfg : ∀ w ∈ D, f (g w) = w)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ w in {w | w ∈ D ∧ infDist w (frontier D) ≤ r},
      ENNReal.ofReal (-Real.log ‖g w‖)) ≤ ENNReal.ofReal (layerGreenConstant * r ^ 2) := by
  have hImage : f '' ball (0 : ℂ) 1 = D := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hmf hz
    · intro hw
      exact ⟨g w, hmg hw, hfg w hw⟩
  have hi : InjOn f (ball 0 1) := by
    intro z hz w hw he
    simpa only [hgf z hz, hgf w hw] using congrArg g he
  have hgrange : DifferentiableOn ℂ g (f '' ball (0 : ℂ) 1) := by rw [hImage]; exact hg
  have hne : ∀ z ∈ ball (0 : ℂ) 1, deriv f z ≠ 0 :=
    fun z hz => chart_deriv_ne_zero hD hd hg hmf hgf hz
  let L := {w | w ∈ D ∧ infDist w (frontier D) ≤ r}
  let T := {z | z ∈ ball (0 : ℂ) 1 ∧ diskWeight z * ‖deriv f z‖ ≤ (256 * Real.pi) * r}
  have hL : MeasurableSet L := hD.measurableSet.inter
    (measurableSet_le (continuous_infDist_pt (frontier D)).measurable measurable_const)
  have hT : MeasurableSet T := conformal_layer_measurable hd _
  have hLD : L ⊆ D := fun w hw => hw.1
  have hTB : T ⊆ ball (0 : ℂ) 1 := fun z hz => hz.1
  have hscale : 0 < (256 * Real.pi) * r := by positivity
  calc
    _ = ∫⁻ w in D, L.indicator (fun w => ENNReal.ofReal (-Real.log ‖g w‖)) w := by
      rw [lintegral_indicator hL, Measure.restrict_restrict hL, inter_eq_left.mpr hLD]
    _ = ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv f z‖ ^ 2) *
        L.indicator (fun w => ENNReal.ofReal (-Real.log ‖g w‖)) (f z) := by
      rw [← hImage]
      exact conformal_disk_area_change hd hi _
    _ ≤ ∫⁻ z in ball (0 : ℂ) 1, T.indicator
        (fun z => ENNReal.ofReal ((-Real.log ‖z‖) * ‖deriv f z‖ ^ 2)) z := by
      apply setLIntegral_mono' measurableSet_ball
      intro z hz
      by_cases hl : f z ∈ L
      · have ht : z ∈ T := ⟨hz, (disk_radius_le_frontier_distance hD hfront hd hi hImage hz).trans
          (mul_le_mul_of_nonneg_left hl.2 (by positivity))⟩
        simp only [indicator_of_mem hl, indicator_of_mem ht, hgf z hz]
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        exact le_of_eq (congrArg ENNReal.ofReal (mul_comm _ _))
      · simp only [indicator_of_notMem hl, mul_zero]
        exact bot_le
    _ = ∫⁻ z in T, ENNReal.ofReal ((-Real.log ‖z‖) * ‖deriv f z‖ ^ 2) := by
      rw [lintegral_indicator hT, Measure.restrict_restrict hT, inter_eq_left.mpr hTB]
    _ ≤ ENNReal.ofReal ((8 * Real.pi / layerExponent) * ((256 * Real.pi) * r) ^ 2) :=
      disk_conformal_layer_green_le hd hi hgrange hgf hne hscale
    _ = _ := by congr 1; unfold layerGreenConstant; ring

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

noncomputable def halfPlaneToDisk (w v : ℂ) : ℂ := (v - w) / (v - star w)

lemma halfPlane_denominator_ne {w v : ℂ} (hw : 0 < w.im) (hv : 0 < v.im) :
    v - star w ≠ 0 := by
  intro he
  have hh := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at hh
  linarith

lemma halfPlaneToDisk_maps {w : ℂ} (hw : 0 < w.im) :
    MapsTo (halfPlaneToDisk w) upperHalfPlane (ball 0 1) := by
  intro v hv
  exact mem_ball_zero_iff.mpr (upper_mobius_norm_lt_one hv hw)

lemma halfPlaneToDisk_differentiable {w : ℂ} (hw : 0 < w.im) :
    DifferentiableOn ℂ (halfPlaneToDisk w) upperHalfPlane :=
  (differentiableOn_id.sub_const w).div (differentiableOn_id.sub_const (star w))
    (fun _ hv => halfPlane_denominator_ne hw hv)

lemma halfPlaneToDisk_diskToHalfPlane {w ζ : ℂ} (hw : 0 < w.im)
    (hζ : ζ ∈ ball (0 : ℂ) 1) : halfPlaneToDisk w (diskToHalfPlane w ζ) = ζ := by
  have hn : w - star w ≠ 0 := halfPlane_denominator_ne hw hw
  have hd := disk_denominator_ne hζ
  have hv := halfPlane_denominator_ne hw (diskToHalfPlane_maps hw hζ)
  unfold halfPlaneToDisk
  apply (div_eq_iff hv).mpr
  unfold diskToHalfPlane
  field_simp [hd]
  ring

lemma diskToHalfPlane_deriv {w ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) :
    HasDerivAt (diskToHalfPlane w) ((w - star w) / (1 - ζ) ^ 2) ζ := by
  have hh := ((hasDerivAt_const ζ w).sub ((hasDerivAt_id ζ).const_mul (star w))).div
    ((hasDerivAt_const ζ 1).sub (hasDerivAt_id ζ)) (disk_denominator_ne hζ)
  convert hh using 1 <;> first | rfl | (dsimp; ring)

lemma diskToHalfPlane_second_zero (w : ℂ) :
    HasDerivAt (deriv (diskToHalfPlane w)) (2 * (w - star w)) 0 := by
  have heq : deriv (diskToHalfPlane w) =ᶠ[𝓝 (0 : ℂ)]
      (fun ζ => (w - star w) / (1 - ζ) ^ 2) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1))] with ζ hζ
    exact (diskToHalfPlane_deriv hζ).deriv
  have hh := (hasDerivAt_const (0 : ℂ) (w - star w)).div
    (((hasDerivAt_const (0 : ℂ) 1).sub (hasDerivAt_id 0)).pow 2) (by norm_num : ((1 : ℂ) - 0) ^ 2 ≠ 0)
  have hh' : HasDerivAt (fun ζ : ℂ => (w - star w) / (1 - ζ) ^ 2)
      (2 * (w - star w)) 0 := by
    convert hh using 1 <;> first | rfl | (norm_num; ring)
  exact hh'.congr_of_eventuallyEq heq

end SLEExactGauge

end

 
section

open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
namespace SLEExactGauge

 

noncomputable def halfPlaneGreen (z w : ℂ) : ℝ :=
  Real.log ‖(z - conj w) / (z - w)‖

lemma hasDerivWithinAt_log_norm {f : ℝ → ℂ} {v : ℂ} {S : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f v S t) (h0 : f t ≠ 0) :
    HasDerivWithinAt (fun s => Real.log ‖f s‖) (v / f t).re S t := by
  have hh := (hf.norm_sq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr h0))).div_const 2
  have he : (fun s => Real.log (‖f s‖ ^ 2) / 2) = (fun s => Real.log ‖f s‖) := by
    funext s
    rw [Real.log_pow]
    ring
  rw [he] at hh
  apply hh.congr_deriv
  rw [Complex.div_re, Complex.sq_norm, real_inner_eq_re_inner ℂ]
  simp only [inner, Complex.star_def, RCLike.re_to_complex, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma hasDerivWithinAt_conj {f : ℝ → ℂ} {v : ℂ} {S : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f v S t) :
    HasDerivWithinAt (fun s => conj (f s)) (conj v) S t := by
  exact Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t hf

lemma hasDerivWithinAt_log_norm_div {f g : ℝ → ℂ} {v w : ℂ} {S : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f v S t) (hg : HasDerivWithinAt g w S t)
    (hf0 : f t ≠ 0) (hg0 : g t ≠ 0) :
    HasDerivWithinAt (fun s => Real.log ‖f s / g s‖)
      (v / f t - w / g t).re S t := by
  apply (hasDerivWithinAt_log_norm (hf.div hg hg0) (div_ne_zero hf0 hg0)).congr_deriv
  congr 1
  change ((v * g t - f t * w) / g t ^ 2) / (f t / g t) = v / f t - w / g t
  field_simp

lemma green_decrease_algebra (z w : ℂ) (hz : 0 < z.im) (hw : 0 < w.im) (hne : z ≠ w) :
    ((2 / z - conj (2 / w)) / (z - conj w) - (2 / z - 2 / w) / (z - w)).re =
      -4 * (z.im / ‖z‖ ^ 2) * (w.im / ‖w‖ ^ 2) := by
  have hz0 : z ≠ 0 := fun h => by simp only [h, Complex.zero_im, lt_self_iff_false] at hz
  have hw0 : w ≠ 0 := fun h => by simp only [h, Complex.zero_im, lt_self_iff_false] at hw
  have hcw0 : conj w ≠ 0 := by simpa using hw0
  have hn : z - w ≠ 0 := sub_ne_zero.mpr hne
  have hn' : z - conj w ≠ 0 := by
    intro hh
    have he := congrArg Complex.im (sub_eq_zero.mp hh)
    simp only [Complex.conj_im] at he
    linarith
  have h₁ : (2 / z - conj (2 / w)) / (z - conj w) = -2 / (z * conj w) := by
    simp only [map_div₀, map_ofNat]
    field_simp
    ring
  have h₂ : (2 / z - 2 / w) / (z - w) = -2 / (z * w) := by
    field_simp
    ring
  rw [h₁, h₂]
  simp only [Complex.sub_re, Complex.div_re, Complex.neg_re, Complex.neg_im,
    Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.normSq_mul, Complex.normSq_conj, Complex.sq_norm]
  norm_num
  ring

 

end SLEExactGauge
end
end
end

end OAI
