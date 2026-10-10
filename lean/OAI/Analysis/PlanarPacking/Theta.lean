import OAI.Analysis.PlanarPacking.GaussianSeries

namespace OAI

namespace SharpPlanar
open Complex
noncomputable def thetaKernel (a : ℂ) (r : ℝ) (k j : ℤ) : ℂ :=
  Complex.exp (-(Real.pi:ℂ)*a*(((j:ℂ)+(k:ℂ)/2)^2/(r:ℂ)+(r:ℂ)*(k:ℂ)^2))
lemma theta_first {a : ℂ} (ha : 0<a.re) {r : ℝ} (hr : 0<r) (k : ℤ) :
    (∑' j : ℤ, thetaKernel a r k j) =
      1/(a/(r:ℂ))^(1/2:ℂ) * ∑' m : ℤ,
        Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2-
          (Real.pi:ℂ)*(a*r)*(k:ℂ)^2+(Real.pi:ℂ)*Complex.I*m*k) := by
  have hA : 0<(a/(r:ℂ)).re := by
    rw [Complex.div_ofReal_re]; exact div_pos ha hr
  have hh := gaussian_shift_poisson hA ((k:ℝ)/2)
  have he (j : ℤ) : thetaKernel a r k j =
      Complex.exp (-(Real.pi:ℂ)*(a*r)*(k:ℂ)^2)*
        Complex.exp (-(Real.pi:ℂ)*(a/(r:ℂ))*((j:ℂ)+(k:ℂ)/2)^2) := by
    rw [thetaKernel,← Complex.exp_add]; congr 1; ring
  simp_rw [he]
  rw [tsum_mul_left]
  push_cast at hh
  rw [hh]
  calc
    _ = 1/(a/(r:ℂ))^(1/2:ℂ) * (Complex.exp (-(Real.pi:ℂ)*(a*r)*(k:ℂ)^2)*
        ∑' m : ℤ, Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2+
          2*(Real.pi:ℂ)*Complex.I*m*((k:ℂ)/2))) := by ring
    _ = _ := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr; intro m
      rw [← Complex.exp_add]; congr 1; ring
lemma theta_second {a : ℂ} (ha : 0<a.re) {r : ℝ} (hr : 0<r) (m : ℤ) :
    (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2-
          (Real.pi:ℂ)*(a*r)*(k:ℂ)^2+(Real.pi:ℂ)*Complex.I*m*k)) =
      1/(a*r)^(1/2:ℂ) * ∑' n : ℤ, thetaKernel (1/a) r (-m) n := by
  have hB : 0<(a*(r:ℂ)).re := by
    rw [Complex.mul_re]; simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_pos ha hr
  have an : a≠0 := by intro h; simp [h] at ha
  have rn : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  have hh := Complex.tsum_exp_neg_quadratic hB (Complex.I*(m:ℂ)/2)
  have he (k : ℤ) :
      Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2-
          (Real.pi:ℂ)*(a*r)*(k:ℂ)^2+(Real.pi:ℂ)*Complex.I*m*k) =
      Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2)*
        Complex.exp (-(Real.pi:ℂ)*(a*r)*(k:ℂ)^2+
          2*(Real.pi:ℂ)*(Complex.I*(m:ℂ)/2)*k) := by
    rw [← Complex.exp_add]; congr 1; ring
  simp_rw [he]
  rw [tsum_mul_left,hh]
  calc
    _ = 1/(a*r)^(1/2:ℂ) * (Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2)*
        ∑' n : ℤ, Complex.exp (-(Real.pi:ℂ)/(a*r)*((n:ℂ)+Complex.I*(Complex.I*(m:ℂ)/2))^2)) := by ring
    _ = _ := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr; intro n
      rw [thetaKernel,← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring_nf
      simp [Complex.I_sq]
lemma thetaKernel_norm (a : ℂ) (r : ℝ) (k j : ℤ) :
    ‖thetaKernel a r k j‖ = Real.exp (-Real.pi*a.re*((j+(k:ℝ)/2)^2/r+r*(k:ℝ)^2)) := by
  rw [thetaKernel,Complex.norm_exp]
  congr 1
  simp only [← Complex.ofReal_intCast,← Complex.ofReal_pow,← Complex.ofReal_add,
    ← Complex.ofReal_mul,← Complex.ofReal_div,← Complex.ofReal_ofNat,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,Complex.neg_im,mul_zero,zero_mul,sub_zero,neg_zero]

lemma theta_quadratic_bound {r : ℝ} (hr : 0<r) (x y : ℝ) :
    min (1/r) r/2*(x^2+y^2) ≤ (x+y/2)^2/r+r*y^2 := by
  have hm : 0 ≤ min (1/r) r := (lt_min (one_div_pos.mpr hr) hr).le
  calc
    _ ≤ min (1/r) r*((x+y/2)^2+y^2) := by
      have hh : (x^2+y^2)/2 ≤ (x+y/2)^2+y^2 := by
        nlinarith [sq_nonneg (x+y),sq_nonneg y]
      nlinarith [mul_le_mul_of_nonneg_left hh hm]
    _ ≤ _ := by
      simp only [mul_add,div_eq_mul_inv,one_mul]
      exact add_le_add
        (by nlinarith [mul_le_mul_of_nonneg_right (min_le_left r⁻¹ r) (sq_nonneg (x+y/2))])
        (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg y))

lemma thetaKernel_summable {a : ℂ} (ha : 0<a.re) {r : ℝ} (hr : 0<r) :
    Summable (fun p : ℤ×ℤ => thetaKernel a r p.1 p.2) := by
  let c : ℝ := Real.pi*a.re*(min (1/r) r/2)
  have hc : 0<c := by dsimp [c]; exact mul_pos (mul_pos Real.pi_pos ha) (div_pos (lt_min (one_div_pos.mpr hr) hr) (by norm_num))
  have hh := (real_integer_gaussian_summable hc).mul_of_nonneg
    (real_integer_gaussian_summable hc) (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)
  apply Summable.of_norm_bounded hh
  intro p
  rw [thetaKernel_norm,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have ht := theta_quadratic_bound hr (p.2:ℝ) (p.1:ℝ)
  dsimp [c]
  nlinarith [mul_le_mul_of_nonneg_left ht (mul_pos Real.pi_pos ha).le]

lemma theta_poisson {a : ℂ} (ha : 0<a.re) {r : ℝ} (hr : 0<r) :
    (∑' p : ℤ×ℤ, thetaKernel a r p.1 p.2) =
      1/a * ∑' p : ℤ×ℤ, thetaKernel (1/a) r p.1 p.2 := by
  have an : a≠0 := by intro h; simp [h] at ha
  have hA : 0<(a/(r:ℂ)).re := by rw [Complex.div_ofReal_re]; exact div_pos ha hr
  have hAn : a/(r:ℂ)≠0 := by intro h; simp [h] at hA
  have hAi : 0<((Real.pi:ℂ)/(a/(r:ℂ))).re := by
    rw [div_eq_mul_inv,Complex.mul_re,Complex.inv_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_pos Real.pi_pos (div_pos hA (Complex.normSq_pos.mpr hAn))
  have hB : 0<((Real.pi:ℂ)*(a*r)).re := by
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_mul,sub_zero]
    exact mul_pos Real.pi_pos (mul_pos ha hr)
  have hmid := phase_gaussian_summable hAi hB Real.pi
  have hi : 0<(1/a).re := by
    rw [one_div,Complex.inv_re]; exact div_pos ha (Complex.normSq_pos.mpr an)
  rw [(thetaKernel_summable ha hr).tsum_prod,(thetaKernel_summable hi hr).tsum_prod]
  simp_rw [theta_first ha hr]
  rw [tsum_mul_left]
  have hswap :
      (∑' k : ℤ, ∑' m : ℤ, Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2-
          (Real.pi:ℂ)*(a*r)*(k:ℂ)^2+(Real.pi:ℂ)*Complex.I*m*k)) =
      ∑' m : ℤ, ∑' k : ℤ, Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2-
          (Real.pi:ℂ)*(a*r)*(k:ℂ)^2+(Real.pi:ℂ)*Complex.I*m*k) := by
    exact (show Summable (Function.uncurry fun (m k : ℤ) => Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2-(Real.pi:ℂ)*(a*r)*(k:ℂ)^2+(Real.pi:ℂ)*Complex.I*m*k)) by
      convert hmid using 1
      funext p
      simp only [Function.uncurry]
      ring_nf).tsum_comm
  rw [hswap]
  simp_rw [theta_second ha hr]
  rw [tsum_mul_left,← mul_assoc,one_div_mul_one_div,
    gaussian_scale_half_product an hr]
  congr 1
  exact (Equiv.neg ℤ).tsum_eq (fun k : ℤ => ∑' j : ℤ, thetaKernel (1/a) r k j)

end SharpPlanar

end OAI
