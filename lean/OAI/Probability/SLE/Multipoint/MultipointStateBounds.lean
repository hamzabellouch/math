import OAI.Probability.SLE.Multipoint.MultipointPiecewiseClock

namespace OAI

/-! Deterministic compact bounds for the adapted state and its discount.
Only the Brownian coordinate needs a separate stopping bound. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

lemma lipschitz_state_norm_le {E : Type*} [NormedAddCommGroup E]
    (Q : ℝ → E) (L : ℝ≥0) (hQ : LipschitzWith L Q) (H t : ℝ)
    (ht : 0 ≤ t) (htH : t ≤ H) : ‖Q t‖ ≤ ‖Q 0‖+(L : ℝ)*H := by
  have hd : ‖Q t-Q 0‖ ≤ (L : ℝ)*t := by
    simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht] using hQ.dist_le_mul t 0
  calc
    ‖Q t‖ = ‖(Q t-Q 0)+Q 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖Q t-Q 0‖+‖Q 0‖ := norm_add_le _ _
    _ ≤ (L : ℝ)*H+‖Q 0‖ := add_le_add
      (hd.trans (mul_le_mul_of_nonneg_left htH L.coe_nonneg)) le_rfl
    _ = _ := add_comm _ _

lemma discounted_state_norm_bound {Ω E : Type*} [NormedAddCommGroup E]
    (Q : ℝ → Ω → E) (L : ℝ≥0) (hQ : ∀ ω, LipschitzWith L (fun t => Q t ω))
    (q₀ : E) (hQ0 : ∀ ω, Q 0 ω = q₀)
    (r : ℝ≥0 → Ω → ℝ) (hr : ∀ ω, Measurable (fun t => r t ω))
    (C : ℝ≥0) (hrb : ∀ t ω, |r t ω| ≤ C)
    (B : ℝ≥0 → Ω → ℝ) (χ : Ω → ℝ≥0) (H : ℝ≥0) (hχ : ∀ ω, χ ω ≤ H)
    (M : ℝ) (hB : ∀ ω t, t ≤ χ ω → ‖B t ω‖ ≤ M)
    (ω : Ω) (t : ℝ) (ht : 0 ≤ t) (htχ : t ≤ (χ ω : ℝ)) :
    ‖((Q t ω,discountClock r t ω),B t.toNNReal ω)‖ ≤
      max (max (‖q₀‖+(L : ℝ)*(H : ℝ)) ((C : ℝ)*(H : ℝ))) M := by
  have htH : t ≤ (H : ℝ) := htχ.trans (by exact_mod_cast hχ ω)
  have hq := lipschitz_state_norm_le (fun t => Q t ω) L (hQ ω) H t ht htH
  rw [hQ0 ω] at hq
  have hc := lipschitz_state_norm_le (fun t => discountClock r t ω) C
    (discountClock_lipschitz_of_measurable r hr C hrb ω) H t ht htH
  rw [discountClock_initial, norm_zero, zero_add] at hc
  have hbt : t.toNNReal ≤ χ ω := Real.toNNReal_le_iff_le_coe.mpr htχ
  simp only [Prod.norm_def]
  exact max_le_max (max_le_max hq hc) (hB ω t.toNNReal hbt)

end SLEExactGauge.Multipoint

end

end OAI
