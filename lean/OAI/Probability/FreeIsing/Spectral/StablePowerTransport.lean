import Mathlib

namespace OAI

noncomputable section

namespace Problem367.StablePowerTransport

variable {𝕜 E V : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]

theorem pow_apply_intertwiner
    (N : V →L[𝕜] V) (T : E →L[𝕜] E) (R : E →L[𝕜] V)
    (hNR : ∀ z, N (R z) = R (T z)) (n : ℕ) (z : E) :
    (N ^ n) (R z) = R ((T ^ n) z) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, ih, hNR]

theorem norm_pow_apply_le_of_stable_intertwiner
    (N : V →L[𝕜] V) (T : E →L[𝕜] E) (R : E →L[𝕜] V)
    (hNR : ∀ z, N (R z) = R (T z))
    {κ : ℝ} (hκ : 0 < κ) (hR : ∀ z, κ * ‖z‖ ≤ ‖R z‖)
    (n : ℕ) {x : V} (hx : x ∈ R.range) :
    ‖(N ^ n) x‖ ≤ (‖R‖ / κ) * ‖T ^ n‖ * ‖x‖ := by
  obtain ⟨z, hz⟩ := hx
  change R z = x at hz
  subst x
  rw [pow_apply_intertwiner N T R hNR]
  have hzbound : ‖z‖ ≤ ‖R z‖ / κ := by
    apply (le_div_iff₀ hκ).mpr
    simpa only [mul_comm] using hR z
  calc
    ‖R ((T ^ n) z)‖ ≤ ‖R‖ * ‖(T ^ n) z‖ := R.le_opNorm _
    _ ≤ ‖R‖ * (‖T ^ n‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left ((T ^ n).le_opNorm z) (norm_nonneg _)
    _ ≤ ‖R‖ * (‖T ^ n‖ * (‖R z‖ / κ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hzbound (norm_nonneg _)) (norm_nonneg _)
    _ = (‖R‖ / κ) * ‖T ^ n‖ * ‖R z‖ := by ring

theorem norm_pow_apply_le_of_model_bound
    (N : V →L[𝕜] V) (T : E →L[𝕜] E) (R : E →L[𝕜] V)
    (hNR : ∀ z, N (R z) = R (T z))
    {κ : ℝ} (hκ : 0 < κ) (hR : ∀ z, κ * ‖z‖ ≤ ‖R z‖)
    (n : ℕ) {C : ℝ} (hC : ‖T ^ n‖ ≤ C) {x : V} (hx : x ∈ R.range) :
    ‖(N ^ n) x‖ ≤ ((‖R‖ / κ) * C) * ‖x‖ := by
  apply (norm_pow_apply_le_of_stable_intertwiner N T R hNR hκ hR n hx).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hC (div_nonneg (norm_nonneg _) hκ.le)) (norm_nonneg _)

end Problem367.StablePowerTransport

end

end OAI
