import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFourierMomentBound

namespace OAI

/-! # Uniform bounds for the physical Fourier jet through order two -/

namespace DefocusingNLS

noncomputable def expandingJetBound (a k : ℝ) : ℝ :=
  expandingEmbeddingBound a (k + 2) + expandingEmbeddingBound a k * Real.sqrt (2 ^ (6 - a) + 1)

theorem summable_expandingFourier_jet (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    Summable (fun n => (1 + (‖n‖ / L) ^ 2) * ‖expandingFourierCoefficient a (k + 2) L f n‖) := by
  simpa only [add_mul, one_mul] using
    (summable_norm_expandingFourierCoefficient a (k + 2) L ha ha1 (by linarith) hL f).add
      (summable_expandingFourier_secondMoment a k L ha ha1 hk hL f)

theorem tsum_expandingFourier_jet_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    (∑' n, (1 + (‖n‖ / L) ^ 2) * ‖expandingFourierCoefficient a (k + 2) L f n‖) ≤
      expandingJetBound a k * ‖f‖ := by
  simp_rw [add_mul, one_mul]
  rw [Summable.tsum_add
    (summable_norm_expandingFourierCoefficient a (k + 2) L ha ha1 (by linarith) hL f)
    (summable_expandingFourier_secondMoment a k L ha ha1 hk hL f)]
  have h0 := tsum_norm_expandingFourierCoefficient_le a (k + 2) L ha ha1 (by linarith) hL f
  have h2 := tsum_expandingFourier_secondMoment_le a k L ha ha1 hk hL f
  dsimp [expandingJetBound]
  calc
    _ ≤ expandingEmbeddingBound a (k + 2) * ‖f‖ +
        expandingEmbeddingBound a k * Real.sqrt (2 ^ (6 - a) + 1) * ‖f‖ := add_le_add h0 h2
    _ = _ := by ring

theorem sum_expandingFourier_jet_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2)
    (S : Finset frequencyLattice) :
    (∑ n ∈ S, (1 + (‖n‖ / L) ^ 2) * ‖expandingFourierCoefficient a (k + 2) L f n‖) ≤
      expandingJetBound a k * ‖f‖ :=
  ((summable_expandingFourier_jet a k L ha ha1 hk hL f).sum_le_tsum S
    (fun n _ => by positivity)).trans (tsum_expandingFourier_jet_le a k L ha ha1 hk hL f)

end DefocusingNLS

end OAI
