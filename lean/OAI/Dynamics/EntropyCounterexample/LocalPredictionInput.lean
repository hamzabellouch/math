import OAI.Dynamics.EntropyCounterexample.PredictionInput
import OAI.Dynamics.EntropyCounterexample.InputSeries

namespace OAI

noncomputable section

namespace Problem340

theorem norm_add_fderiv_predictionSummand_scaled_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : E → ℝ} {β : ℝ → ℝ} {T : ℕ → E → ℝ} {Φ : ℕ → E → F}
    {A D J K B L : ℝ} {n : ℕ} {x : E}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β (T n x))
    (hT : DifferentiableAt ℝ (T n) x) (hΦ : DifferentiableAt ℝ (Φ n) x)
    (hα₀ : ‖α x‖ ≤ 1) (hβ₀ : ‖β (T n x)‖ ≤ 1) (hΦ₀ : ‖Φ n x‖ ≤ 1)
    (hα₁ : ‖fderiv ℝ α x‖ ≤ A)
    (hβ₁ : ‖fderiv ℝ β (T n x)‖ ≤ D)
    (hT₁ : ‖fderiv ℝ (T n) x‖ ≤ J * B ^ (n + 1))
    (hΦ₁ : ‖fderiv ℝ (Φ n) x‖ ≤ K * (1 + 2 ^ (n + 2))) :
    ‖predictionSummand α β T Φ L n x‖ +
      ‖fderiv ℝ (predictionSummand α β T Φ L n) x‖ ≤
        predictionMajorant ((1 + A + D * J + K) / 10) B L n := by
  have hβT : ‖fderiv ℝ (β ∘ T n) x‖ ≤ (D * J) * B ^ (n + 1) := by
    have h := (norm_fderiv_comp_le hβ hT).trans
      (mul_le_mul hβ₁ hT₁ (norm_nonneg _) hD)
    simpa only [mul_assoc] using h
  have hm := norm_add_fderiv_predictionTerm_le hα (hβ.comp x hT) hΦ
    (c := (L⁻¹) ^ n / 10) (by positivity)
    hα₀ hβ₀ hΦ₀ hα₁ hβT hΦ₁
  change ‖predictionSummand α β T Φ L n x‖ +
    ‖fderiv ℝ (predictionSummand α β T Φ L n) x‖ ≤
      (L⁻¹) ^ n / 10 * (1 + A + (D * J) * B ^ (n + 1) + K * (1 + 2 ^ (n + 2))) at hm
  apply hm.trans
  have hDJ : 0 ≤ D * J := mul_nonneg hD hJ
  have hpB : 0 ≤ B ^ (n + 1) := pow_nonneg hB _
  have hp2 : 0 ≤ (2 : ℝ) ^ (n + 2) := by positivity
  have he : 1 + A + (D * J) * B ^ (n + 1) + K * (1 + 2 ^ (n + 2)) ≤
      (1 + A + D * J + K) * (1 + B ^ (n + 1) + 2 ^ (n + 2)) := by
    nlinarith [mul_nonneg (show 0 ≤ 1 + A + K by linarith) hpB,
      mul_nonneg (show 0 ≤ 1 + A + D * J by linarith) hp2]
  have hfinal := mul_le_mul_of_nonneg_left he (show 0 ≤ (L⁻¹) ^ n / 10 by positivity)
  convert hfinal using 1
  simp only [predictionMajorant]
  ring

theorem contDiffOn_predictionInput
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} {α : E → ℝ} {β : ℝ → ℝ}
    {T : ℕ → E → ℝ} {Φ : ℕ → E → F} {A D J K B L : ℝ}
    (hs : IsOpen s)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hJ : 0 ≤ J) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hBL : B < L) (hL : 2 < L)
    (hα : ContDiffOn ℝ 1 α s) (hβ : ContDiff ℝ 1 β)
    (hT : ∀ n, ContDiffOn ℝ 1 (T n) s)
    (hΦ : ∀ n, ContDiffOn ℝ 1 (Φ n) s)
    (hα₀ : ∀ x ∈ s, ‖α x‖ ≤ 1)
    (hβ₀ : ∀ n x, x ∈ s → ‖β (T n x)‖ ≤ 1)
    (hΦ₀ : ∀ n x, x ∈ s → ‖Φ n x‖ ≤ 1)
    (hα₁ : ∀ x ∈ s, ‖fderiv ℝ α x‖ ≤ A)
    (hβ₁ : ∀ n x, x ∈ s → ‖fderiv ℝ β (T n x)‖ ≤ D)
    (hT₁ : ∀ n x, x ∈ s → ‖fderiv ℝ (T n) x‖ ≤ J * B ^ (n + 1))
    (hΦ₁ : ∀ n x, x ∈ s → ‖fderiv ℝ (Φ n) x‖ ≤ K * (1 + 2 ^ (n + 2))) :
    ContDiffOn ℝ 1 (fun x => ∑' n, predictionSummand α β T Φ L n x) s := by
  apply contDiffOn_tsum_of_norm_add_fderiv_bound hs
    (u := predictionMajorant ((1 + A + D * J + K) / 10) B L)
  · intro n
    exact (hα.smul ((hβ.comp_contDiffOn (hT n)).smul (hΦ n))).const_smul _
  · exact summable_predictionMajorant hB hBL hL
  · intro n x hx
    exact norm_add_fderiv_predictionSummand_scaled_le hA hD hJ hK hB (by linarith)
      ((hα.differentiableOn_one x hx).differentiableAt (hs.mem_nhds hx))
      (hβ.differentiable_one _)
      (((hT n).differentiableOn_one x hx).differentiableAt (hs.mem_nhds hx))
      (((hΦ n).differentiableOn_one x hx).differentiableAt (hs.mem_nhds hx))
      (hα₀ x hx) (hβ₀ n x hx) (hΦ₀ n x hx)
      (hα₁ x hx) (hβ₁ n x hx) (hT₁ n x hx) (hΦ₁ n x hx)

end Problem340

end

end OAI
