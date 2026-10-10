import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphApplication

namespace OAI

/-! # The stable graph from the normalized linear data and a small remainder -/

namespace DefocusingNLS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_stableGraph_of_small_remainder
    (ζ : ℕ → F →L[ℝ] E) (π : ℕ → E →L[ℝ] F)
    (A : ℕ → E →L[ℝ] E) (D R : F →L[ℝ] F)
    (hR : ‖R‖ ≤ 1) (hinv : ∀ v, D (R v) = v)
    (hπζ : ∀ n v, π n (ζ n v) = v)
    (hA : ∀ n, ‖stableProjectedBlock (ζ n) (ζ (n + 1))
      (π n) (π (n + 1)) (A n)‖ ≤ 1 / 8)
    (hB : ∀ n, ‖stableMixedBlock (ζ n) (ζ (n + 1)) (π (n + 1)) (A n)‖ ≤ 1 / 16)
    (C ρ ε r : ℝ) (hC : 0 < C) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hrsmall : 2 * r ≤ 1)
    (hζ : ∀ n, ‖ζ n‖ ≤ 1) (hπ : ∀ n, ‖π n‖ ≤ C)
    (hP : ∀ n, ‖stableFrameProjection (ζ n) (π n)‖ ≤ C)
    (he : ∀ n, ‖(π (n + 1)).comp (A n) - D.comp (π n)‖ ≤ 1 / 128)
    (h : ℕ → E → E)
    (hlip : ∀ n v w, ‖v‖ ≤ 2 * ρ → ‖w‖ ≤ 2 * ρ →
      ‖h n v - h n w‖ ≤ (1 / (128 * (C + 1))) * ‖v - w‖)
    (hzero : ∀ n, ‖h n 0‖ ≤ ε * r ^ n)
    (w₀ : E) (hw₀ : π 0 w₀ = 0) (hsmall : ‖w₀‖ + 2 * (C * ε) ≤ ρ / 2) :
    ∃ z : ℕ → E,
      stableFrameProjection (ζ 0) (π 0) (z 0) = w₀ ∧
      (∀ n, z (n + 1) = A n (z n) + h n (z n)) ∧
      (∀ n, ‖z n‖ ≤ (4 * (‖w₀‖ + 2 * (C * ε))) * (1 / 2 : ℝ) ^ n) := by
  have hκ : 0 ≤ 1 / (128 * (C + 1)) := by positivity
  have hCκ : C * (1 / (128 * (C + 1))) ≤ 1 / 128 := by
    rw [one_div, ← div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hN (n : ℕ) (v w : E × F) (hv : ‖v‖ ≤ ρ) (hw : ‖w‖ ≤ ρ) :=
    stableFramePointSources_lipschitz ζ π A D h 1 C C (1 / 128)
      (1 / (128 * (C + 1))) ρ (2 * ρ) zero_le_one hC.le hC.le (by norm_num) hκ
      hζ (fun n => hP (n + 1)) (fun n => hπ (n + 1)) he (by ring_nf; rfl) hlip n v w hv hw
  have hz (n : ℕ) := stableFramePointSources_zero ζ π A D h C C ε r hC.le hC.le
    (fun n => hP (n + 1)) (fun n => hπ (n + 1)) hzero n
  obtain ⟨z, hz0, hzstep, hzbound⟩ := exists_stableGraph_actual_endpoint_sequence ζ π A D R hR hinv
    hπζ hA hB h w₀ hw₀ ρ (C * ε) 1 r hρ (mul_nonneg hC.le hε) zero_le_one hr hrsmall hζ
    (fun n v w hv hw => (hN n v w hv hw).1.trans
      (mul_le_mul_of_nonneg_right (by nlinarith : C * (1 / (128 * (C + 1))) * (1 + 1) ≤ 1 / 16)
        (norm_nonneg _)))
    (fun n v w hv hw => (hN n v w hv hw).2.trans
      (mul_le_mul_of_nonneg_right (by nlinarith :
        (1 / 128 + C * (1 / (128 * (C + 1)))) * (1 + 1) ≤ 1 / 16) (norm_nonneg _)))
    (fun n => (hz n).1) (fun n => (hz n).2) hsmall
  refine ⟨z, hz0, hzstep, fun n => (hzbound n).trans_eq ?_⟩
  ring

end DefocusingNLS

end OAI
