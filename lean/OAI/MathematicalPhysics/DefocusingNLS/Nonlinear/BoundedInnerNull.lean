import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingOddCompactness

namespace OAI

/-! # Pairing a bounded sequence with a strongly vanishing sequence -/

open Filter Topology

namespace DefocusingNLS

theorem tendsto_inner_of_bounded_null {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u v : ℕ → H) (M : ℝ) (hu : ∀ n, ‖u n‖ ≤ M) (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun n => inner ℝ (u n) (v n)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have ht : Tendsto (fun n => M * ‖v n‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hv.norm.const_mul M
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => (norm_inner_le_norm (𝕜 := ℝ) (u n) (v n)).trans
      (mul_le_mul_of_nonneg_right (hu n) (norm_nonneg _))) ht

end DefocusingNLS

end OAI
