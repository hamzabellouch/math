import OAI.Analysis.Triangular.Energy.Theta

namespace OAI

namespace SharpPlanar
open scoped BigOperators
open Complex

lemma gaussian_shift_poisson {a : ℂ} (ha : 0 < a.re) (d : ℝ) :
    (∑' n : ℤ, Complex.exp (-(Real.pi:ℂ)*a*((n:ℂ)+d)^2)) =
      1/a^(1/2:ℂ) * ∑' n : ℤ,
        Complex.exp (-(Real.pi:ℂ)/a*(n:ℂ)^2+2*(Real.pi:ℂ)*Complex.I*n*d) := by
  have hane : a≠0 := by intro h; simp [h] at ha
  have hh := Complex.tsum_exp_neg_quadratic ha (-a*d)
  have hleft (n : ℤ) :
      Complex.exp (-(Real.pi:ℂ)*a*((n:ℂ)+d)^2) =
        Complex.exp (-(Real.pi:ℂ)*a*d^2) *
          Complex.exp (-(Real.pi:ℂ)*a*(n:ℂ)^2+2*(Real.pi:ℂ)*(-a*d)*n) := by
    rw [← Complex.exp_add]; congr 1; ring
  simp_rw [hleft]
  rw [tsum_mul_left,hh]
  calc
    _ = 1/a^(1/2:ℂ) * (Complex.exp (-(Real.pi:ℂ)*a*d^2) *
        ∑' n : ℤ, Complex.exp (-(Real.pi:ℂ)/a*((n:ℂ)+Complex.I*(-a*d))^2)) := by ring
    _ = _ := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [← Complex.exp_add]
      congr 1
      field_simp
      ring_nf
      simp [Complex.I_sq]

lemma integer_gaussian_summable {a : ℂ} (ha : 0<a.re) :
    Summable (fun n : ℤ => Complex.exp (-a*(n:ℂ)^2)) := by
  have hh := (isLittleO_exp_neg_mul_sq_cocompact ha (-2)).isBigO.comp_tendsto
    Int.tendsto_coe_cofinite
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1:ℝ)<2)) hh

lemma real_integer_gaussian_summable {a : ℝ} (ha : 0<a) :
    Summable (fun n : ℤ => Real.exp (-a*(n:ℝ)^2)) :=
  TriangularUniversal.Theta.intGaussian_summable ha

lemma gaussian_scale_half_product {a : ℂ} (ha : a≠0) {r : ℝ} (hr : 0<r) :
    (a/(r:ℂ))^(1/2:ℂ)*(a*r)^(1/2:ℂ)=a := by
  have hrn : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero (div_ne_zero ha hrn),
    Complex.cpow_def_of_ne_zero (mul_ne_zero ha hrn)]
  rw [← Complex.exp_add]
  have hh : Complex.log (a/(r:ℂ))=(Complex.log a)-(Real.log r:ℂ) := by
    rw [div_eq_mul_inv,← Complex.ofReal_inv,Complex.log_mul_ofReal r⁻¹ (inv_pos.mpr hr) a ha,
      Real.log_inv,Complex.ofReal_neg]
    ring
  rw [hh,Complex.log_mul_ofReal r hr a ha]
  convert Complex.exp_log ha using 2; ring

lemma phase_gaussian_summable {A B : ℂ} (hA : 0<A.re) (hB : 0<B.re) (c : ℝ) :
    Summable (fun p : ℤ×ℤ => Complex.exp (-A*(p.1:ℂ)^2-B*(p.2:ℂ)^2+
      (c:ℂ)*Complex.I*p.1*p.2)) := by
  apply Summable.of_norm
  have hh := (real_integer_gaussian_summable hA).mul_of_nonneg
    (real_integer_gaussian_summable hB) (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)
  convert hh using 1
  funext p
  rw [Complex.norm_exp,← Real.exp_add]
  congr 1
  simp only [← Complex.ofReal_intCast,← Complex.ofReal_pow,
    Complex.add_re,Complex.sub_re,Complex.neg_re,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  ring

end SharpPlanar

end OAI
