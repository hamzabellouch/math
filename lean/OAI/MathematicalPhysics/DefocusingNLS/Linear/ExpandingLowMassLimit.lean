import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLowInterpolation

namespace OAI

/-! # Vanishing lower energy from bounded Sobolev norm and vanishing mass -/

open Filter Topology

namespace DefocusingNLS

theorem expandingLowEnergy_norm_le (a k L : ℝ) (hL : 1 ≤ L) (f : FourierL2) :
    ‖expandingLowEnergy a k L hL f‖ ≤ ‖f‖ := by
  have he := expandingEnergy_norm_sq a k L hL f
  nlinarith [sq_nonneg ‖expandingHighEnergy a k L hL f‖, norm_nonneg f,
    norm_nonneg (expandingLowEnergy a k L hL f)]

theorem tendsto_expandingLowEnergy_of_mass (a M : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ))
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (hmass : Tendsto (fun n => ‖expandingPhysicalMassVector a N (L n) ha ha1 hN (hL n) (f n)‖)
      atTop (𝓝 0)) :
    Tendsto (fun n => expandingLowEnergy a N (L n) (hL n) (f n)) atTop (𝓝 0) := by
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hf 0)
  have hs : Tendsto (fun n => ‖expandingLowEnergy a N (L n) (hL n) (f n)‖ ^ 2)
      atTop (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro r hr
      exact Eventually.of_forall (fun n => hr.trans_le (sq_nonneg _))
    · intro ε hε
      let δ := ε / (2 * (M ^ 2 + 1))
      have hδ : 0 < δ := by dsimp [δ]; positivity
      obtain ⟨C, _, hc⟩ := expandingLowEnergy_interpolation a δ N ha ha1 hN hδ
      have hz : Tendsto (fun n => C *
          ‖expandingPhysicalMassVector a N (L n) ha ha1 hN (hL n) (f n)‖ ^ 2) atTop (𝓝 0) := by
        simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using (hmass.pow 2).const_mul C
      have he := hz.eventually (gt_mem_nhds (show 0 < ε / 2 by positivity))
      have hδM : δ * M ^ 2 ≤ ε / 2 := by
        have hi : δ * (2 * (M ^ 2 + 1)) = ε := div_mul_cancel₀ _ (by positivity)
        nlinarith [hδ.le]
      filter_upwards [he] with n hn
      have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hf n) 2) hδ.le
      have hi := hc (L n) (hL n) (f n)
      linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

end DefocusingNLS

end OAI
