import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace TriangularUniversal.Theta

lemma intGaussian_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => Real.exp (-a * (n : ℝ)^2)) := by
  have h := (isLittleO_exp_neg_mul_sq_cocompact
    (show 0 < (a : ℂ).re from ha) (-2)).isBigO.comp_tendsto Int.tendsto_coe_cofinite
  have H : Summable (fun n : ℤ => Complex.exp (-(a : ℂ) * (n : ℂ)^2)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
      (by simpa only [Function.comp_def, Complex.ofReal_intCast] using h)
  simpa [Complex.norm_exp, pow_two, Complex.mul_re, Complex.mul_im] using H.norm

lemma real_Q_ge (m n : ℝ) : (m^2+n^2)/2 ≤ m^2+m*n+n^2 := by nlinarith [sq_nonneg (m+n)]

lemma triangular_summable {c : ℂ} (hc : 0 < c.re) :
    Summable (fun p : ℤ × ℤ => Complex.exp (-Real.pi*c*
      ((p.1:ℂ)^2+(p.1:ℂ)*p.2+(p.2:ℂ)^2))) := by
  have hg := intGaussian_summable (div_pos (mul_pos Real.pi_pos hc) (by norm_num : (0:ℝ)<2))
  apply Summable.of_norm
  refine (hg.mul_of_nonneg hg (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)).of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  rintro ⟨m,n⟩
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.intCast_re, Complex.intCast_im, Complex.add_re, Complex.add_im,
    pow_two, Complex.mul_re, Complex.mul_im, mul_zero, zero_mul, sub_zero, add_zero]
  nlinarith [mul_le_mul_of_nonneg_left (real_Q_ge (m:ℝ) (n:ℝ)) (mul_pos Real.pi_pos hc).le]

lemma inv_re_pos {c : ℂ} (hc : 0 < c.re) : 0 < (c⁻¹).re := by
  rw [Complex.inv_re]
  exact div_pos hc (Complex.normSq_pos.mpr (by intro h; simp [h] at hc))

def theta (c : ℂ) : ℂ := ∑' p : ℤ × ℤ,
  Complex.exp (-Real.pi*c*((p.1:ℂ)^2+(p.1:ℂ)*p.2+(p.2:ℂ)^2))


lemma middle_summable {c : ℂ} (hc : 0 < c.re) :
    Summable (fun p : ℤ × ℤ => Complex.exp
      (-3*Real.pi*c*(p.2:ℂ)^2/4 + Real.pi*Complex.I*p.1*p.2 - Real.pi/c*(p.1:ℂ)^2)) := by
  have ha := intGaussian_summable (mul_pos Real.pi_pos (inv_re_pos hc))
  have hb := intGaussian_summable (show 0 < 3*Real.pi*c.re/4 by positivity)
  apply Summable.of_norm
  refine (ha.mul_of_nonneg hb (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)).of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  rintro ⟨j,n⟩
  rw [Complex.norm_exp, ← Real.exp_add]
  apply le_of_eq
  congr 1
  simp only [div_eq_mul_inv, pow_two, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.intCast_re, Complex.intCast_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im,
    Complex.inv_re, Complex.inv_im]
  norm_num
  ring

lemma first_step {c : ℂ} (hc : 0 < c.re) (n : ℤ) :
    (∑' m : ℤ, Complex.exp (-Real.pi*c*((m:ℂ)^2+(m:ℂ)*n+(n:ℂ)^2))) =
      1 / c^(1/2:ℂ) * ∑' j : ℤ, Complex.exp
        (-3*Real.pi*c*(n:ℂ)^2/4 + Real.pi*Complex.I*j*n - Real.pi/c*(j:ℂ)^2) := by
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  have h := Complex.tsum_exp_neg_quadratic hc (-c*n/2)
  have hsplit (m : ℤ) :
      Complex.exp (-Real.pi*c*((m:ℂ)^2+(m:ℂ)*n+(n:ℂ)^2)) =
        Complex.exp (-Real.pi*c*(n:ℂ)^2) *
        Complex.exp (-Real.pi*c*(m:ℂ)^2+2*Real.pi*(-c*n/2)*m) := by
    rw [← Complex.exp_add]; congr 1; ring
  simp_rw [hsplit]
  rw [tsum_mul_left, h, ← mul_assoc, mul_comm (Complex.exp _) _, mul_assoc,
    ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro j
  rw [← Complex.exp_add]
  congr 1
  field_simp [hc0]
  ring_nf
  norm_num [show Complex.I^4 = 1 by norm_num [pow_succ, Complex.I_sq], Complex.I_sq]
  ring


lemma second_step {c : ℂ} (hc : 0 < c.re) (j : ℤ) :
    (∑' n : ℤ, Complex.exp
      (-3*Real.pi*c*(n:ℂ)^2/4 + Real.pi*Complex.I*j*n - Real.pi/c*(j:ℂ)^2)) =
      1 / (3*c/4)^(1/2:ℂ) * ∑' k : ℤ,
        Complex.exp (-Real.pi*(4/(3*c))*((j:ℂ)^2-(j:ℂ)*k+(k:ℂ)^2)) := by
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  have hpos : 0 < (3*c/4).re := by simp; linarith
  have h := Complex.tsum_exp_neg_quadratic hpos (Complex.I*j/2)
  have hsplit (n : ℤ) : Complex.exp
      (-3*Real.pi*c*(n:ℂ)^2/4 + Real.pi*Complex.I*j*n - Real.pi/c*(j:ℂ)^2) =
      Complex.exp (-Real.pi/c*(j:ℂ)^2) *
      Complex.exp (-Real.pi*(3*c/4)*(n:ℂ)^2+2*Real.pi*(Complex.I*j/2)*n) := by
    rw [← Complex.exp_add]; congr 1; ring
  simp_rw [hsplit]
  rw [tsum_mul_left, h, ← mul_assoc, mul_comm (Complex.exp _) _, mul_assoc,
    ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro k
  rw [← Complex.exp_add]
  congr 1
  field_simp [hc0]
  ring_nf
  norm_num [show Complex.I^4 = 1 by norm_num [pow_succ, Complex.I_sq], Complex.I_sq]
  ring


lemma dual_re_pos {c : ℂ} (hc : 0 < c.re) : 0 < (4/(3*c)).re := by
  have : (4/(3*c):ℂ) = (4/3:ℝ) * c⁻¹ := by push_cast; ring
  rw [this, Complex.re_ofReal_mul]
  exact mul_pos (by norm_num) (inv_re_pos hc)

lemma theta_raw {c : ℂ} (hc : 0 < c.re) :
    theta c = (1/c^(1/2:ℂ)) * (1/(3*c/4)^(1/2:ℂ)) * theta (4/(3*c)) := by
  have hstart : theta c = ∑' n : ℤ, ∑' m : ℤ,
      Complex.exp (-Real.pi*c*((m:ℂ)^2+(m:ℂ)*n+(n:ℂ)^2)) := by
    rw [theta, (triangular_summable hc).tsum_prod]
    apply tsum_congr; intro n
    apply tsum_congr; intro m
    congr 1; ring
  rw [hstart]
  simp_rw [first_step hc]
  rw [tsum_mul_left, (middle_summable hc).tsum_comm]
  simp_rw [second_step hc]
  rw [tsum_mul_left, ← mul_assoc]
  congr 1
  rw [theta, (triangular_summable (dual_re_pos hc)).tsum_prod]
  calc
    _ = (∑' j : ℤ, ∑' k : ℤ, Complex.exp
        (-Real.pi*(4/(3*c))*(((-j:ℤ):ℂ)^2+((-j:ℤ):ℂ)*k+(k:ℂ)^2))) := by
      apply tsum_congr; intro j
      apply tsum_congr; intro k
      congr 1; push_cast; ring
    _ = _ := by
      simpa only using! (Equiv.neg ℤ).tsum_eq (fun j => ∑' k : ℤ, Complex.exp
        (-Real.pi*(4/(3*c))*((j:ℂ)^2+(j:ℂ)*k+(k:ℂ)^2)))

lemma cpow_scale {c : ℂ} (hc0 : c ≠ 0) :
    (3*c/4)^(1/2:ℂ) = ((Real.sqrt 3 / 2 : ℝ):ℂ) * c^(1/2:ℂ) := by
  have hscale : (3*c/4:ℂ) = ((3/4:ℝ):ℂ)*c := by push_cast; ring
  rw [hscale, Complex.cpow_def_of_ne_zero (mul_ne_zero (by norm_num) hc0),
    Complex.log_ofReal_mul (by norm_num) hc0, add_mul, Complex.exp_add,
    ← Complex.cpow_def_of_ne_zero hc0]
  congr 1
  have hpow : ((3/4:ℝ):ℂ)^(1/2:ℂ) = ((Real.sqrt 3/2:ℝ):ℂ) := by
    calc
      _ = Complex.ofReal ((3/4:ℝ)^(1/2:ℝ)) := by
        convert (Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 3/4) (1/2)).symm using 1; push_cast; rfl
      _ = _ := by
        congr 1
        rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num)]
        rw [show Real.sqrt (4 : ℝ) = 2 from
          (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)]
  rw [Complex.cpow_def_of_ne_zero (by norm_num), ← Complex.ofReal_log (by norm_num)] at hpow
  exact hpow


lemma theta_transform {c : ℂ} (hc : 0 < c.re) :
    theta c = 2/((Real.sqrt 3:ℂ)*c) * theta (4/(3*c)) := by
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  rw [theta_raw hc]
  congr 1
  rw [div_mul_div_comm, one_mul, cpow_scale hc0]
  have h : c^(1/2:ℂ) * (((Real.sqrt 3/2:ℝ):ℂ) * c^(1/2:ℂ)) =
      ((Real.sqrt 3/2:ℝ):ℂ)*c := by
    rw [mul_left_comm, ← Complex.cpow_add _ _ hc0]
    norm_num
  rw [h]
  push_cast
  ring

end TriangularUniversal.Theta

end

end OAI
