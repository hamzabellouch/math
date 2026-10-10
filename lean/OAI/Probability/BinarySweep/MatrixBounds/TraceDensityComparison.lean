import Mathlib
import OAI.Probability.BinarySweep.MatrixBounds.Whitening

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I W : Type*} [Fintype I] [DecidableEq I] [Fintype W]

omit [DecidableEq I] in
lemma trace_re_real_smul (a : ℝ) (X : Matrix I I ℂ) :
    ((a : ℂ) • X).trace.re = a * X.trace.re := by
  simp [Matrix.trace_smul,Complex.mul_re]

omit [DecidableEq I] in
lemma trace_re_nat_smul (a : ℕ) (X : Matrix I I ℂ) :
    ((a : ℂ) • X).trace.re = a * X.trace.re := by
  simpa only [Complex.ofReal_natCast] using trace_re_real_smul (a:ℝ) X

lemma trace_density_whitening (R Q P C : Matrix I I ℂ) (d a : ℝ)
    (V : W → Matrix I I ℂ) (hR : R.PosSemidef) (hC : C.IsHermitian)
    (hcap : (C*Q*C-(d:ℂ)•(Q*P)).PosSemidef)
    (hdom : ((a:ℂ)•∑w, V w-Q).PosSemidef) :
    d*(R*Q*P).trace.re ≤ a*∑w, (C*R*C*V w).trace.re := by
  have h1 := trace_product_re_mono hR hcap
  rw [Matrix.mul_smul,trace_re_real_smul,← mul_assoc R Q P] at h1
  have h2 := hdom.mul_mul_conjTranspose_same C
  rw [hC.eq,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_sum,Matrix.sum_mul] at h2
  have h3 := trace_product_re_mono hR h2
  rw [Matrix.mul_smul,trace_re_real_smul,Matrix.mul_sum,Matrix.trace_sum,
    Complex.re_sum] at h3
  have he (w : W) : (R*(C*V w*C)).trace = (C*R*C*V w).trace := by
    rw [← mul_assoc R (C*V w) C,Matrix.trace_mul_cycle]
    congr 1
    noncomm_ring
  simp only [he] at h3
  exact h1.trans h3

lemma trace_right_density_domination (R S : Matrix I I ℂ) (a : ℝ)
    (U : W → Matrix I I ℂ) (hS : S.PosSemidef)
    (hdom : ((a:ℂ)•∑w, U w-R).PosSemidef) :
    (R*S).trace.re ≤ a * ∑w, (U w*S).trace.re := by
  have ht := trace_product_re_mono hS hdom
  rw [Matrix.mul_smul,trace_re_real_smul,Matrix.mul_sum,Matrix.trace_sum,Complex.re_sum,
    Matrix.trace_mul_comm S R] at ht
  simpa only [Matrix.trace_mul_comm S] using ht

end BinaryCoordinateSweeps.Density

end

end OAI
