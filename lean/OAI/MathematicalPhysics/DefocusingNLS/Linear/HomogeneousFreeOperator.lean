import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeFourier

namespace OAI

/-! # Bounded whole-space free operators on the exact completion

The Fourier-side Schwartz action extends through a dense map to Y. The bound
for nonnegative time is exactly exp(-a s/2).
-/

open MeasureTheory
open scoped SchwartzMap ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousFrequencyEmbedding (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) : 𝓢(E, ℂ) →L[ℂ] HomogeneousY a k := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  exact SchwartzMap.toLpCLM ℂ ℂ 2 (homogeneousFourierMeasure a k)

theorem homogeneousFrequencyEmbedding_dense (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    DenseRange (homogeneousFrequencyEmbedding a k ha ha1 hk) := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  let := homogeneousFourierMeasure_locallyFinite a k ha1 hk
  exact SchwartzMap.denseRange_toLpCLM (F := ℂ) (μ := homogeneousFourierMeasure a k)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)

theorem homogeneousFrequencyEmbedding_norm_sq (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ : 𝓢(E, ℂ)) :
    ‖homogeneousFrequencyEmbedding a k ha ha1 hk ψ‖ ^ 2 =
      ((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
        (homogeneousFrequencyEnergy (6 - a) ψ + homogeneousFrequencyEnergy k ψ) := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  obtain ⟨χ, hχ⟩ := radianFourierKernel_surjective ψ
  have h := homogeneousSchwartzEmbedding_norm_sq a k ha ha1 hk χ
  simpa only [homogeneousSchwartzEmbedding_apply, hχ, homogeneousFrequencyEmbedding,
    SchwartzMap.toLpCLM_apply, homogeneousFrequencyEnergy, homogeneousFourierEnergy,
    ← radianFourierKernel_apply] using h

theorem homogeneousFrequencyEmbedding_norm_sq_integral (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ : 𝓢(E, ℂ)) :
    ‖homogeneousFrequencyEmbedding a k ha ha1 hk ψ‖ ^ 2 =
      ∫ ξ, ‖ψ ξ‖ ^ 2 ∂homogeneousFourierMeasure a k := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  have hn := SchwartzMap.norm_toLp' (f := ψ)
    (μ := homogeneousFourierMeasure a k) (p := 2) (by norm_num) (by norm_num)
  have he : ‖homogeneousFrequencyEmbedding a k ha ha1 hk ψ‖ =
      Real.sqrt (∫ ξ, ‖ψ ξ‖ ^ 2 ∂homogeneousFourierMeasure a k) := by
    simpa only [homogeneousFrequencyEmbedding, SchwartzMap.toLpCLM_apply,
      ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow, one_div] using hn
  rw [he, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]

noncomputable def homogeneousFreeBound (a k s : ℝ) : ℝ :=
  max (Real.exp (-a * s / 2)) (Real.exp ((6 - 2 * a - k) * s / 2))

private theorem exp_half_sq (x : ℝ) : Real.exp (x / 2) ^ (2 : ℕ) = Real.exp x := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem homogeneousFreeFourier_norm_bound (a b k s : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ : 𝓢(E, ℂ)) :
    ‖homogeneousFrequencyEmbedding a k ha ha1 hk (homogeneousFreeFourier a b s ψ)‖ ≤
      homogeneousFreeBound a k s * ‖homogeneousFrequencyEmbedding a k ha ha1 hk ψ‖ := by
  let c := ((2 * Real.pi) ^ (12 : ℕ))⁻¹
  let E₁ := homogeneousFrequencyEnergy (6 - a) ψ
  let E₂ := homogeneousFrequencyEnergy k ψ
  let C := homogeneousFreeBound a k s
  have hC : 0 ≤ C := le_trans (Real.exp_nonneg _) (le_max_left _ _)
  have hE₁ : 0 ≤ E₁ := integral_nonneg (fun _ => by positivity)
  have hE₂ : 0 ≤ E₂ := integral_nonneg (fun _ => by positivity)
  have hc : 0 ≤ c := by positivity
  have h₁ : Real.exp (-a * s) ≤ C ^ 2 := by
    rw [← exp_half_sq]
    exact (sq_le_sq₀ (Real.exp_nonneg _) hC).mpr (le_max_left _ _)
  have h₂ : Real.exp ((6 - 2 * a - k) * s) ≤ C ^ 2 := by
    rw [← exp_half_sq]
    exact (sq_le_sq₀ (Real.exp_nonneg _) hC).mpr (le_max_right _ _)
  have hn := homogeneousFrequencyEmbedding_norm_sq a k ha ha1 hk ψ
  have hn' := homogeneousFrequencyEmbedding_norm_sq a k ha ha1 hk
    (homogeneousFreeFourier a b s ψ)
  rw [homogeneousFreeFourier_energy, homogeneousFreeFourier_energy] at hn'
  have he : 6 - 2 * a - (6 - a) = -a := by ring
  rw [he] at hn'
  change ‖homogeneousFrequencyEmbedding a k ha ha1 hk ψ‖ ^ 2 = c * (E₁ + E₂) at hn
  change ‖homogeneousFrequencyEmbedding a k ha ha1 hk (homogeneousFreeFourier a b s ψ)‖ ^ 2 =
    c * (Real.exp (-a * s) * E₁ + Real.exp ((6 - 2 * a - k) * s) * E₂) at hn'
  have hs : ‖homogeneousFrequencyEmbedding a k ha ha1 hk (homogeneousFreeFourier a b s ψ)‖ ^ 2 ≤
      (C * ‖homogeneousFrequencyEmbedding a k ha ha1 hk ψ‖) ^ 2 := by
    rw [hn', mul_pow, hn]
    exact mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_right h₁ hE₁) (mul_le_mul_of_nonneg_right h₂ hE₂)) hc |>.trans_eq (by ring)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp hs

noncomputable def homogeneousFreeOperator (a b k s : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) : HomogeneousY a k →L[ℂ] HomogeneousY a k :=
  ((homogeneousFrequencyEmbedding a k ha ha1 hk).comp
    (homogeneousFreeFourier a b s)).toLinearMap.extendOfNorm
      (homogeneousFrequencyEmbedding a k ha ha1 hk).toLinearMap

theorem homogeneousFreeOperator_on_Schwartz (a b k s : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ : 𝓢(E, ℂ)) :
    homogeneousFreeOperator a b k s ha ha1 hk
      (homogeneousFrequencyEmbedding a k ha ha1 hk ψ) =
        homogeneousFrequencyEmbedding a k ha ha1 hk (homogeneousFreeFourier a b s ψ) :=
  LinearMap.extendOfNorm_eq (homogeneousFrequencyEmbedding_dense a k ha ha1 hk)
    ⟨homogeneousFreeBound a k s, homogeneousFreeFourier_norm_bound a b k s ha ha1 hk⟩ ψ

theorem homogeneousFreeOperator_norm_le (a b k s : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    ‖homogeneousFreeOperator a b k s ha ha1 hk f‖ ≤ homogeneousFreeBound a k s * ‖f‖ :=
  LinearMap.norm_extendOfNorm_apply_le (homogeneousFrequencyEmbedding_dense a k ha ha1 hk)
    (homogeneousFreeBound a k s) (homogeneousFreeFourier_norm_bound a b k s ha ha1 hk) f

/-- The exact forward decay in the manuscript's homogeneous norm. -/
theorem homogeneousFreeOperator_forward_bound (a b k s : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hs : 0 ≤ s) (f : HomogeneousY a k) :
    ‖homogeneousFreeOperator a b k s ha ha1 hk f‖ ≤ Real.exp (-a * s / 2) * ‖f‖ := by
  have he : homogeneousFreeBound a k s = Real.exp (-a * s / 2) := by
    apply max_eq_left
    apply Real.exp_le_exp.mpr
    nlinarith
  simpa only [he] using homogeneousFreeOperator_norm_le a b k s ha ha1 hk f

end DefocusingNLS

end OAI
