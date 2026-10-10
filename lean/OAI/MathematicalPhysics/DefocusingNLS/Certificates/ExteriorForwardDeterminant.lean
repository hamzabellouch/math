import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorFormBounds

namespace OAI

/-! The uniform determinant margin used by the exterior quotient disk. -/

open Matrix
namespace DefocusingNLS.ExteriorCertificate

private theorem step_normSq (b : ℝ) (n : ℕ) :
    Complex.normSq ((-Complex.I*(b : ℂ)+(n : ℂ)) *
      (-Complex.I*(b : ℂ)+(n : ℂ)-5)) =
      ((n : ℝ)^2+b^2)*(((n : ℝ)-5)^2+b^2) := by
  rw [Complex.normSq_mul]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.sub_re,
    Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.natCast_re,Complex.natCast_im,zero_mul,neg_zero,zero_add,
    add_zero]
  norm_num
  ring

theorem forward_det_normSq (b Z : ℝ) (K : ℕ) :
    Complex.normSq (forwardProduct 5 (Complex.I*(Z : ℂ)) (-Complex.I*(b : ℂ)) K).det =
      ∏ n ∈ Finset.range K, ((n : ℝ)^2+b^2)*(((n : ℝ)-5)^2+b^2) := by
  induction K with
  | zero => simp [forwardProduct]
  | succ K ih =>
    rw [forwardProduct,Matrix.det_mul,Complex.normSq_mul,det_forwardMatrix,ih,
      Finset.prod_range_succ,step_normSq]
    ring

theorem exterior_forward_det_bound (b Z : ℝ) (hb : |100000000*b-33477607| ≤ 2) :
    ‖(forwardProduct 5 (Complex.I*(Z : ℂ)) (-Complex.I*(b : ℂ)) 5).det‖ < 1130 := by
  have hb' := abs_le.mp hb
  have hb2 : b^2 ≤ (335/1000 : ℝ)^2 := by nlinarith
  have hp : (∏ n ∈ Finset.range 5, ((n : ℝ)^2+b^2)*(((n : ℝ)-5)^2+b^2)) ≤
      ∏ n ∈ Finset.range 5,
        ((n : ℝ)^2+(335/1000 : ℝ)^2)*(((n : ℝ)-5)^2+(335/1000 : ℝ)^2) := by
    apply Finset.prod_le_prod₀
    · intro n _
      positivity
    · intro n _
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hconst : (∏ n ∈ Finset.range 5,
      ((n : ℝ)^2+(335/1000 : ℝ)^2)*(((n : ℝ)-5)^2+(335/1000 : ℝ)^2)) < 1130^2 := by
    norm_num [Finset.prod_range_succ]
  rw [← forward_det_normSq b Z 5,Complex.normSq_eq_norm_sq] at hp
  nlinarith [norm_nonneg (forwardProduct 5 (Complex.I*(Z : ℂ)) (-Complex.I*(b : ℂ)) 5).det]

end DefocusingNLS.ExteriorCertificate

end OAI
