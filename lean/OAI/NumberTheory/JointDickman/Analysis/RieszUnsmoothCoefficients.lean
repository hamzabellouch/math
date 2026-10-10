import OAI.NumberTheory.JointDickman.Analysis.RieszLogPolynomial

namespace OAI

/-! # The coefficients obtained by differentiating a Riesz expansion -/
namespace JointDickman
open Finset

noncomputable def rieszUnsmoothCoefficients (b : ℕ → ℝ) (z : ℝ) : ℕ → ℝ
  | 0 => 2*b 0
  | j+1 => 2*b (j+1)+(z-1-j)*b j

theorem rieszLogDerivative_eq (b : ℕ → ℝ) (z : ℝ) (K : ℕ) (x : ℝ) :
    rieszLogDerivative b z K x =
      x*((∑ j ∈ range (K+1), rieszUnsmoothCoefficients b z j*(Real.log x)^(z-1-j)) +
        (z-1-K)*b K*(Real.log x)^(z-1-K-1)) := by
  induction K with
  | zero =>
    simp only [rieszLogDerivative,zero_add,sum_range_one,rieszUnsmoothCoefficients,
      Nat.cast_zero,sub_zero,logRieszDerivative]
    ring
  | succ K ih =>
    have hstep : rieszLogDerivative b z (K+1) x = rieszLogDerivative b z K x +
        b (K+1)*logRieszDerivative (z-1-(K+1:ℕ)) x := by
      unfold rieszLogDerivative
      rw [sum_range_succ]
    have hsum : (∑ j ∈ range (K+1+1), rieszUnsmoothCoefficients b z j*(Real.log x)^(z-1-j)) =
        (∑ j ∈ range (K+1), rieszUnsmoothCoefficients b z j*(Real.log x)^(z-1-j)) +
          rieszUnsmoothCoefficients b z (K+1)*(Real.log x)^(z-1-(K+1:ℕ)) := sum_range_succ _ _
    change rieszLogDerivative b z (K+1) x = _
    rw [hstep,ih,hsum]
    simp only [rieszUnsmoothCoefficients,logRieszDerivative,Nat.cast_add,Nat.cast_one]
    rw [show z-1-((K:ℝ)+1) = z-1-K-1 by ring]
    ring

end JointDickman

end OAI
