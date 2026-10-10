import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleContourDegree

namespace OAI

/-! # Rouché's theorem for the spectral counting rectangle

The specialization of Ahlfors, *Complex Analysis*, third edition,
Chapter 4, §5.2, p. 153, Corollary following Theorem 18 follows from the finite
analytic divisor, Cauchy's theorem, and the boundary logarithm of the quotient.
-/

namespace DefocusingNLS

theorem rectangle_rouche : RectangleRouche := by
  intro V hV f g hf hg hn
  have hnf (z : ℂ) (hz : z ∈ countingRectangleBoundary V) : f z ≠ 0 :=
    norm_pos_iff.mp ((norm_nonneg _).trans_lt (hn z hz))
  have hng (z : ℂ) (hz : z ∈ countingRectangleBoundary V) : g z ≠ 0 := by
    intro he
    have hi := hn z hz
    simp [he] at hi
  have he := countingBoundaryIntegral_rouche V hV f g hf hg hn
  rw [countingBoundaryIntegral_eq_degree V hV f hf hnf,
    countingBoundaryIntegral_eq_degree V hV g hg hng] at he
  have hd : countingZeroDegree V f = countingZeroDegree V g := by
    exact_mod_cast mul_right_cancel₀ (countingBoundaryIntegral_inv_ne_zero V hV) he
  rw [rectangleZeroCount_eq_degree V hV f hf hnf,
    rectangleZeroCount_eq_degree V hV g hg hng, hd]

end DefocusingNLS

end OAI
