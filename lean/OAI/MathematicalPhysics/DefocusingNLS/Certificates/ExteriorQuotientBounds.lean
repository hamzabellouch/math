import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorQuotientDisk
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorForwardDeterminant

namespace OAI

/-! The certified real and imaginary bounds for the outgoing quotient. -/

namespace DefocusingNLS.ExteriorCertificate

private theorem quotient_component_re (c : ℂ) (d : ℝ) :
    (c/(d : ℂ)).re = c.re/d := by
  simp [div_eq_mul_inv, ← Complex.ofReal_inv,Complex.mul_re]

private theorem quotient_component_im (c : ℂ) (d : ℝ) :
    (c/(d : ℂ)).im = c.im/d := by
  simp [div_eq_mul_inv, ← Complex.ofReal_inv,Complex.mul_im]

theorem exterior_quotient_real_bound (b Z : ℝ)
    (hb : |100000000*b-33477607| ≤ 2) (hZ : 2704/1000 ≤ Z) :
    ((-deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6) (-Complex.I*(Z : ℂ)))/
      regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ))).re < 43/1000 := by
  let j := (-deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6) (-Complex.I*(Z : ℂ)))/
    regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ))
  let c := exteriorForm b Z 1 0
  let d := (exteriorForm b Z 1 1).re
  let D := ‖(forwardProduct 5 (Complex.I*(Z : ℂ)) (-Complex.I*(b : ℂ)) 5).det‖
  have hd : 0 < d := exterior_diagonal_positive b Z hb hZ
  have hnorm : ‖j+c/(d : ℂ)‖ ≤ Z*D/d := exterior_slow_quotient_disk b Z hb hZ
  have hre := (le_abs_self (j+c/(d : ℂ)).re).trans
    ((Complex.abs_re_le_norm _).trans hnorm)
  rw [Complex.add_re,quotient_component_re] at hre
  have hmul := (le_div_iff₀ hd).mp hre
  have he : (j.re+c.re/d)*d=j.re*d+c.re := by
    rw [add_mul,div_mul_cancel₀ _ hd.ne']
  rw [he] at hmul
  have hD : D < 1130 := exterior_forward_det_bound b Z hb
  have hR := exterior_real_bound b Z hb hZ
  have hZD : Z*D < 1130*Z := by nlinarith
  change j.re < 43/1000
  by_contra hn
  have hh := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hd.le
  dsimp only [c,d] at hmul hh
  nlinarith

theorem exterior_quotient_imaginary_positive (b Z : ℝ)
    (hb : |100000000*b-33477607| ≤ 2) (hZ : 3 ≤ Z) :
    0 < ((-deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6) (-Complex.I*(Z : ℂ)))/
      regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ))).im := by
  have hZ' : 2704/1000 ≤ Z := by linarith
  let j := (-deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6) (-Complex.I*(Z : ℂ)))/
    regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ))
  let c := exteriorForm b Z 1 0
  let d := (exteriorForm b Z 1 1).re
  let D := ‖(forwardProduct 5 (Complex.I*(Z : ℂ)) (-Complex.I*(b : ℂ)) 5).det‖
  have hd : 0 < d := exterior_diagonal_positive b Z hb hZ'
  have hnorm : ‖j+c/(d : ℂ)‖ ≤ Z*D/d := exterior_slow_quotient_disk b Z hb hZ'
  have him := (neg_le_abs (j+c/(d : ℂ)).im).trans
    ((Complex.abs_im_le_norm _).trans hnorm)
  rw [Complex.add_im,quotient_component_im] at him
  have hmul := (le_div_iff₀ hd).mp him
  have he : (-(j.im+c.im/d))*d= -j.im*d-c.im := by
    rw [neg_mul,add_mul,div_mul_cancel₀ _ hd.ne']
    ring
  rw [he] at hmul
  have hD : D < 1130 := exterior_forward_det_bound b Z hb
  have hI := exterior_imaginary_bound b Z hb hZ
  have hZD : Z*D < 1130*Z := by nlinarith
  change 0 < j.im
  by_contra hn
  have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hd.le
  dsimp only [c,d] at hmul hh
  nlinarith

end DefocusingNLS.ExteriorCertificate

end OAI
