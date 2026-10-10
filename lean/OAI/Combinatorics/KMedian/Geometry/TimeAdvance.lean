import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalPotential
import OAI.Combinatorics.KMedian.Geometry.MomentAnalysis

namespace OAI

section
section
namespace MetricKMedian.Analytic
open Set

noncomputable def timeRate (x y : ℝ) : ℝ := 2*x*(y-x)*moment 2 x
noncomputable def rateDerivative (x y : ℝ) : ℝ :=
  2*(y-2*x)*moment 2 x-2*x*(y-x)*moment 3 x

 theorem hasDerivAt_timeRate (x y : ℝ) :
    HasDerivAt (fun z => timeRate z y) (rateDerivative x y) x := by
  have h := (((hasDerivAt_id x).const_mul 2).mul
    ((hasDerivAt_const x y).sub (hasDerivAt_id x))).mul (hasDerivAt_moment 2 x)
  convert h using 1 <;> try rfl
  dsimp only [rateDerivative, id_eq, Pi.sub_apply, Pi.mul_apply]
  norm_num only [Nat.reduceAdd]
  ring

theorem abs_timeRate {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : |timeRate x y| ≤ 2 := by
  have hdiff : |y-x| ≤ 1 := abs_le.mpr ⟨by linarith only [hy0, hx1], by linarith only [hy1, hx0]⟩
  have hm0 := moment_nonneg 2 x
  have hm1 := moment_le_one 2 hx0
  rw [timeRate, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
    abs_of_nonneg hx0, abs_of_nonneg hm0]
  have hprod : x*|y-x| ≤ 1 := (mul_le_of_le_one_left (abs_nonneg _) hx1).trans hdiff
  have h := mul_le_mul hprod hm1 hm0 (by norm_num : (0:ℝ) ≤ 1)
  nlinarith only [h]

theorem abs_rateDerivative {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : |rateDerivative x y| ≤ 6 := by
  have hdiff : |y-x| ≤ 1 := abs_le.mpr ⟨by linarith only [hy0, hx1], by linarith only [hy1, hx0]⟩
  have hdiff2 : |y-2*x| ≤ 2 := abs_le.mpr ⟨by linarith only [hy0, hx1], by linarith only [hy1, hx0]⟩
  have hm20 := moment_nonneg 2 x
  have hm21 := moment_le_one 2 hx0
  have hm30 := moment_nonneg 3 x
  have hm31 := moment_le_one 3 hx0
  have hfirst : |2*(y-2*x)*moment 2 x| ≤ 4 := by
    have h := mul_le_mul hdiff2 hm21 hm20 (by norm_num : (0:ℝ) ≤ 2)
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg hm20]
    nlinarith only [h]
  have hsecond : |2*x*(y-x)*moment 3 x| ≤ 2 := by
    have hp := (mul_le_of_le_one_left (abs_nonneg (y-x)) hx1).trans hdiff
    have h := mul_le_mul hp hm31 hm30 (by norm_num : (0:ℝ) ≤ 1)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg hx0, abs_of_nonneg hm30]
    nlinarith only [h]
  exact (abs_sub _ _).trans (by linarith only [hfirst, hsecond])

theorem taylor_error_bound (f f' f'' : ℝ → ℝ) {h C : ℝ}
    (hh : 0 ≤ h) (hC : 0 ≤ C)
    (hf : ∀ t ∈ Icc 0 h, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc 0 h, HasDerivAt f' (f'' t) t)
    (hb : ∀ t ∈ Icc 0 h, |f'' t| ≤ C) :
    |f h-f 0-h*f' 0| ≤ C*h^2 := by
  have hr : ∀ t ∈ Icc 0 h, |f' t-f' 0| ≤ C*h := by
    intro t ht
    have hl := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht => (hf' t ht).hasDerivWithinAt)
      (fun t ht => show ‖f'' t‖ ≤ C from by simpa only [Real.norm_eq_abs] using hb t ⟨ht.1, ht.2.le⟩)
      t ht
    simp only [Real.norm_eq_abs, sub_zero] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left ht.2 hC)
  let r := fun t : ℝ => f t-f 0-t*f' 0
  have hdr : ∀ t ∈ Icc 0 h, HasDerivAt r (f' t-f' 0) t := by
    intro t ht
    convert ((hf t ht).sub_const (f 0)).sub ((hasDerivAt_id t).mul_const (f' 0)) using 1 <;> first | rfl | simp only [one_mul]
  have hd := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hdr t ht).hasDerivWithinAt)
    (fun t ht => show ‖f' t-f' 0‖ ≤ C*h from by simpa only [Real.norm_eq_abs] using hr t ⟨ht.1, ht.2.le⟩)
    h ⟨hh, le_refl _⟩
  simpa only [r, sub_self, zero_mul, sub_zero, Real.norm_eq_abs, pow_two, mul_assoc] using hd

 theorem hasDerivAt_phase (x t : ℝ) :
    HasDerivAt (fun u : ℝ => x*Real.exp (-u)) (-(x*Real.exp (-t))) t := by
  simpa only [neg_mul, mul_neg, mul_one, Pi.neg_apply, id_eq] using (((hasDerivAt_id t).neg).exp).const_mul x

 theorem phase_bounds {x t : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ht : 0 ≤ t) :
    0 ≤ x*Real.exp (-t) ∧ x*Real.exp (-t) ≤ 1 := by
  refine ⟨mul_nonneg hx0 (Real.exp_pos _).le, ?_⟩
  exact (mul_le_of_le_one_left (Real.exp_pos _).le hx1).trans
    (Real.exp_le_one_iff.mpr (by linarith only [ht]))

 theorem hasDerivAt_timeCoefficient (x y t : ℝ) :
    HasDerivAt (fun u => coefficient (x*Real.exp (-u)) y)
      (timeRate (x*Real.exp (-t)) y) t := by
  have h := (hasDerivAt_coefficient (x*Real.exp (-t)) y).comp t (hasDerivAt_phase x t)
  convert h using 1 <;> try rfl
  dsimp only [timeRate]
  ring

theorem coefficient_time_error {x y h : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hh : 0 ≤ h) :
    |coefficient (x*Real.exp (-h)) y-coefficient x y-h*timeRate x y| ≤ 6*h^2 := by
  have hdr : ∀ t ∈ Icc (0:ℝ) h,
      HasDerivAt (fun u => timeRate (x*Real.exp (-u)) y)
        (rateDerivative (x*Real.exp (-t)) y * (-(x*Real.exp (-t)))) t := by
    intro t _
    exact (hasDerivAt_timeRate (x*Real.exp (-t)) y).comp t (hasDerivAt_phase x t)
  have hb : ∀ t ∈ Icc (0:ℝ) h,
      |rateDerivative (x*Real.exp (-t)) y * (-(x*Real.exp (-t)))| ≤ 6 := by
    intro t ht
    have hx := phase_bounds hx0 hx1 ht.1
    rw [abs_mul, abs_neg, abs_of_nonneg hx.1]
    exact (mul_le_mul (abs_rateDerivative hx.1 hx.2 hy0 hy1) hx.2 hx.1
      (by norm_num : (0:ℝ) ≤ 6)).trans (by norm_num)
  have he := taylor_error_bound (fun u => coefficient (x*Real.exp (-u)) y)
    (fun u => timeRate (x*Real.exp (-u)) y)
    (fun t => rateDerivative (x*Real.exp (-t)) y * (-(x*Real.exp (-t)))) hh
    (by norm_num) (fun t _ => hasDerivAt_timeCoefficient x y t) hdr hb
  simpa only [neg_zero, Real.exp_zero, mul_one] using he

end MetricKMedian.Analytic

namespace MetricKMedian.PhysicalPotential
open Analytic
variable {I : Type*}

 theorem potential_time_error {x g b h : ℝ} {d : I → ℝ} {S : Finset I}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) (hy : mass g S ≤ 1) (hh : 0 ≤ h) :
    |potential (x*Real.exp (-h)) g d S b-potential x g d S b-
      h*timeRate x (mass g S)*cost g d S| ≤ 6*h^2*cost g d S := by
  have he := mul_le_mul_of_nonneg_right
    (coefficient_time_error hx0 hx1 (mass_nonneg hg S) hy hh) (cost_nonneg hg hd)
  have hid : potential (x*Real.exp (-h)) g d S b-potential x g d S b-
      h*timeRate x (mass g S)*cost g d S =
      (coefficient (x*Real.exp (-h)) (mass g S)-coefficient x (mass g S)-h*timeRate x (mass g S))*cost g d S := by
    simp only [potential, coefficient_eq]
    ring
  rw [hid, abs_mul, abs_of_nonneg (cost_nonneg hg hd)]
  exact he

end MetricKMedian.PhysicalPotential
end
end

end OAI
