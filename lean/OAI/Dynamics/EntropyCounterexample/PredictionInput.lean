import OAI.Dynamics.EntropyCounterexample.PredictionSeries
import OAI.Dynamics.EntropyCounterexample.InputSeries

namespace OAI

noncomputable section

namespace Problem340

theorem norm_fderiv_smul_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : E → ℝ} {v : E → F} {x : E}
    (ha : DifferentiableAt ℝ a x) (hv : DifferentiableAt ℝ v x) :
    ‖fderiv ℝ (fun y => a y • v y) x‖ ≤
      ‖a x‖ * ‖fderiv ℝ v x‖ + ‖fderiv ℝ a x‖ * ‖v x‖ := by
  rw [fderiv_fun_smul ha hv]
  exact (norm_add_le _ _).trans_eq (by
    rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply])

theorem norm_add_fderiv_predictionTerm_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : E → ℝ} {v : E → F} {x : E} {c A D K : ℝ}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hv : DifferentiableAt ℝ v x) (hc : 0 ≤ c)
    (ha₀ : ‖a x‖ ≤ 1) (hb₀ : ‖b x‖ ≤ 1) (hv₀ : ‖v x‖ ≤ 1)
    (ha₁ : ‖fderiv ℝ a x‖ ≤ A) (hb₁ : ‖fderiv ℝ b x‖ ≤ D)
    (hv₁ : ‖fderiv ℝ v x‖ ≤ K) :
    ‖c • (a x • (b x • v x))‖ +
      ‖fderiv ℝ (fun y => c • (a y • (b y • v y))) x‖ ≤
        c * (1 + A + D + K) := by
  have hA : 0 ≤ A := (norm_nonneg _).trans ha₁
  have hD : 0 ≤ D := (norm_nonneg _).trans hb₁
  have hK : 0 ≤ K := (norm_nonneg _).trans hv₁
  have hbv₀ : ‖b x • v x‖ ≤ 1 := by
    rw [norm_smul]
    nlinarith [norm_nonneg (b x), norm_nonneg (v x)]
  have hbv₁ : ‖fderiv ℝ (fun y => b y • v y) x‖ ≤ D + K := by
    apply (norm_fderiv_smul_le hb hv).trans
    nlinarith [norm_nonneg (b x), norm_nonneg (v x),
      norm_nonneg (fderiv ℝ b x), norm_nonneg (fderiv ℝ v x)]
  have hav₀ : ‖a x • (b x • v x)‖ ≤ 1 := by
    rw [norm_smul]
    nlinarith [norm_nonneg (a x), norm_nonneg (b x • v x)]
  have hav₁ : ‖fderiv ℝ (fun y => a y • (b y • v y)) x‖ ≤ A + D + K := by
    have hh := norm_fderiv_smul_le ha (hb.smul hv)
    change ‖fderiv ℝ (fun y => a y • (b y • v y)) x‖ ≤
      ‖a x‖ * ‖fderiv ℝ (fun y => b y • v y) x‖ +
        ‖fderiv ℝ a x‖ * ‖b x • v x‖ at hh
    apply hh.trans
    calc
      _ ≤ 1 * (D + K) + A * 1 := add_le_add
        (mul_le_mul ha₀ hbv₁ (norm_nonneg _) (by norm_num))
        (mul_le_mul ha₁ hbv₀ (norm_nonneg _) hA)
      _ = A + D + K := by ring
  have hd : DifferentiableAt ℝ (fun y => a y • (b y • v y)) x :=
    ha.fun_smul (hb.fun_smul hv)
  have hcv₀ : ‖c • (a x • (b x • v x))‖ ≤ c := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    nlinarith
  have hcv₁ : ‖fderiv ℝ (fun y => c • (a y • (b y • v y))) x‖ ≤
      c * (A + D + K) := by
    rw [fderiv_fun_const_smul hd c, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hav₁ hc
  nlinarith

theorem norm_fderiv_comp_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : F → G} {x : E}
    (hg : DifferentiableAt ℝ g (f x)) (hf : DifferentiableAt ℝ f x) :
    ‖fderiv ℝ (g ∘ f) x‖ ≤ ‖fderiv ℝ g (f x)‖ * ‖fderiv ℝ f x‖ := by
  rw [fderiv_comp x hg hf]
  exact ContinuousLinearMap.opNorm_comp_le _ _

def predictionSummand
    {E F : Type*} [SMul ℝ F]
    (α : E → ℝ) (β : ℝ → ℝ) (T : ℕ → E → ℝ) (Φ : ℕ → E → F)
    (L : ℝ) (n : ℕ) (x : E) : F :=
  ((L⁻¹) ^ n / 10) • (α x • (β (T n x) • Φ n x))

theorem norm_add_fderiv_predictionSummand_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : E → ℝ} {β : ℝ → ℝ} {T : ℕ → E → ℝ} {Φ : ℕ → E → F}
    {A D K B L : ℝ} {n : ℕ} {x : E}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hK : 0 ≤ K) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β (T n x))
    (hT : DifferentiableAt ℝ (T n) x) (hΦ : DifferentiableAt ℝ (Φ n) x)
    (hα₀ : ‖α x‖ ≤ 1) (hβ₀ : ‖β (T n x)‖ ≤ 1) (hΦ₀ : ‖Φ n x‖ ≤ 1)
    (hα₁ : ‖fderiv ℝ α x‖ ≤ A)
    (hβ₁ : ‖fderiv ℝ β (T n x)‖ ≤ D)
    (hT₁ : ‖fderiv ℝ (T n) x‖ ≤ B ^ (n + 1))
    (hΦ₁ : ‖fderiv ℝ (Φ n) x‖ ≤ K * (1 + 2 ^ (n + 2))) :
    ‖predictionSummand α β T Φ L n x‖ +
      ‖fderiv ℝ (predictionSummand α β T Φ L n) x‖ ≤
        predictionMajorant ((1 + A + D + K) / 10) B L n := by
  have hβT : ‖fderiv ℝ (β ∘ T n) x‖ ≤ D * B ^ (n + 1) := by
    exact (norm_fderiv_comp_le hβ hT).trans
      (mul_le_mul hβ₁ hT₁ (norm_nonneg _) hD)
  have hm := norm_add_fderiv_predictionTerm_le hα (hβ.comp x hT) hΦ
    (c := (L⁻¹) ^ n / 10) (by positivity)
    hα₀ hβ₀ hΦ₀ hα₁ hβT hΦ₁
  change ‖predictionSummand α β T Φ L n x‖ +
    ‖fderiv ℝ (predictionSummand α β T Φ L n) x‖ ≤
      (L⁻¹) ^ n / 10 * (1 + A + D * B ^ (n + 1) + K * (1 + 2 ^ (n + 2))) at hm
  apply hm.trans
  have hpB : 0 ≤ B ^ (n + 1) := pow_nonneg hB _
  have hp2 : 0 ≤ (2 : ℝ) ^ (n + 2) := by positivity
  have he : 1 + A + D * B ^ (n + 1) + K * (1 + 2 ^ (n + 2)) ≤
      (1 + A + D + K) * (1 + B ^ (n + 1) + 2 ^ (n + 2)) := by
    nlinarith [mul_nonneg (show 0 ≤ 1 + A + K by linarith) hpB,
      mul_nonneg (show 0 ≤ 1 + A + D by linarith) hp2]
  have hs := mul_le_mul_of_nonneg_left he (show 0 ≤ (L⁻¹) ^ n / 10 by positivity)
  convert hs using 1
  simp only [predictionMajorant]
  ring

theorem contDiff_one_predictionInput
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {α : E → ℝ} {β : ℝ → ℝ} {T : ℕ → E → ℝ} {Φ : ℕ → E → F}
    {A D K B L : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hBL : B < L) (hL : 2 < L)
    (hα : ContDiff ℝ 1 α) (hβ : ContDiff ℝ 1 β)
    (hT : ∀ n, ContDiff ℝ 1 (T n)) (hΦ : ∀ n, ContDiff ℝ 1 (Φ n))
    (hα₀ : ∀ x, ‖α x‖ ≤ 1) (hβ₀ : ∀ t, ‖β t‖ ≤ 1)
    (hΦ₀ : ∀ n x, ‖Φ n x‖ ≤ 1)
    (hα₁ : ∀ x, ‖fderiv ℝ α x‖ ≤ A)
    (hβ₁ : ∀ t, ‖fderiv ℝ β t‖ ≤ D)
    (hT₁ : ∀ n x, ‖fderiv ℝ (T n) x‖ ≤ B ^ (n + 1))
    (hΦ₁ : ∀ n x, ‖fderiv ℝ (Φ n) x‖ ≤ K * (1 + 2 ^ (n + 2))) :
    ContDiff ℝ 1 (fun x => ∑' n, predictionSummand α β T Φ L n x) := by
  apply contDiff_one_tsum_prediction (C := (1 + A + D + K) / 10) hB hBL hL
  · intro n
    exact (hα.smul ((hβ.comp (hT n)).smul (hΦ n))).const_smul _
  · intro n x
    exact norm_add_fderiv_predictionSummand_le hA hD hK hB (by linarith)
      (hα.differentiable_one x) (hβ.differentiable_one _)
      ((hT n).differentiable_one x) ((hΦ n).differentiable_one x)
      (hα₀ x) (hβ₀ _) (hΦ₀ n x) (hα₁ x) (hβ₁ _) (hT₁ n x) (hΦ₁ n x)

theorem contDiffOn_one_predictionInput
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s)
    {α : E → ℝ} {β : ℝ → ℝ} {T : ℕ → E → ℝ} {Φ : ℕ → E → F}
    {A D K B L : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hBL : B < L) (hL : 2 < L)
    (hα : ContDiffOn ℝ 1 α s) (hβ : ContDiff ℝ 1 β)
    (hT : ∀ n, ContDiffOn ℝ 1 (T n) s) (hΦ : ∀ n, ContDiffOn ℝ 1 (Φ n) s)
    (hα₀ : ∀ x ∈ s, ‖α x‖ ≤ 1) (hβ₀ : ∀ t, ‖β t‖ ≤ 1)
    (hΦ₀ : ∀ n x, x ∈ s → ‖Φ n x‖ ≤ 1)
    (hα₁ : ∀ x ∈ s, ‖fderiv ℝ α x‖ ≤ A)
    (hβ₁ : ∀ t, ‖fderiv ℝ β t‖ ≤ D)
    (hT₁ : ∀ n x, x ∈ s → ‖fderiv ℝ (T n) x‖ ≤ B ^ (n + 1))
    (hΦ₁ : ∀ n x, x ∈ s → ‖fderiv ℝ (Φ n) x‖ ≤ K * (1 + 2 ^ (n + 2))) :
    ContDiffOn ℝ 1 (fun x => ∑' n, predictionSummand α β T Φ L n x) s := by
  apply contDiffOn_tsum_of_norm_add_fderiv_bound hs
    (u := predictionMajorant ((1 + A + D + K) / 10) B L)
  · intro n
    exact (hα.smul ((hβ.comp_contDiffOn (hT n)).smul (hΦ n))).const_smul _
  · exact summable_predictionMajorant hB hBL hL
  · intro n x hx
    exact norm_add_fderiv_predictionSummand_le hA hD hK hB (by linarith)
      ((hα.differentiableOn_one x hx).differentiableAt (hs.mem_nhds hx))
      (hβ.differentiable_one _)
      (((hT n).differentiableOn_one x hx).differentiableAt (hs.mem_nhds hx))
      (((hΦ n).differentiableOn_one x hx).differentiableAt (hs.mem_nhds hx))
      (hα₀ x hx) (hβ₀ _) (hΦ₀ n x hx) (hα₁ x hx) (hβ₁ _)
      (hT₁ n x hx) (hΦ₁ n x hx)

end Problem340

end

end OAI
