import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingQuadraticMultiplier

namespace OAI

/-! # Uniform second Fourier moment in physical coordinates -/

namespace DefocusingNLS

theorem summable_expandingFourier_secondMoment (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    Summable (fun n => (‖n‖ / L) ^ 2 * ‖expandingFourierCoefficient a (k + 2) L f n‖) := by
  have h := summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL
    (expandingQuadraticVector a k L ha ha1 hk hL f)
  simpa only [expandingQuadraticVector_coefficient, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_pow, sq_abs] using h

theorem tsum_expandingFourier_secondMoment_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    (∑' n, (‖n‖ / L) ^ 2 * ‖expandingFourierCoefficient a (k + 2) L f n‖) ≤
      expandingEmbeddingBound a k * Real.sqrt (2 ^ (6 - a) + 1) * ‖f‖ := by
  have h := tsum_norm_expandingFourierCoefficient_le a k L ha ha1 hk hL
    (expandingQuadraticVector a k L ha ha1 hk hL f)
  have hn (n : frequencyLattice) :
      ‖expandingFourierCoefficient a k L (expandingQuadraticVector a k L ha ha1 hk hL f) n‖ =
      (‖n‖ / L) ^ 2 * ‖expandingFourierCoefficient a (k + 2) L f n‖ := by
    rw [expandingQuadraticVector_coefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
  simp only [hn] at h
  exact h.trans (by
    have hmul := mul_le_mul_of_nonneg_left (expandingQuadraticVector_norm a k L ha ha1 hk hL f)
      (show 0 ≤ expandingEmbeddingBound a k by unfold expandingEmbeddingBound; positivity)
    nlinarith)

end DefocusingNLS

end OAI
