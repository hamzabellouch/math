import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSchwartzConvolution
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreePhysical

namespace OAI

/-! # The continuous convolution bound in the exact homogeneous norm -/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousAlgebraConstant (a k : ℝ) : ℝ :=
  2 * max (2 ^ (6 - a)) (2 ^ k) *
    Real.sqrt (∫ ξ : E, (homogeneousFourierWeight a k ξ)⁻¹)

theorem homogeneousAlgebraConstant_nonneg (a k : ℝ) :
    0 ≤ homogeneousAlgebraConstant a k := by
  unfold homogeneousAlgebraConstant
  positivity

theorem homogeneousFrequencyEmbedding_L1 (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ : 𝓢(E, ℂ)) :
    (∫ ξ, ‖ψ ξ‖) ≤ Real.sqrt (∫ ξ : E, (homogeneousFourierWeight a k ξ)⁻¹) *
      ‖homogeneousFrequencyEmbedding a k ha ha1 hk ψ‖ := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  have h := (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk
    (ψ.memLp 2 (homogeneousFourierMeasure a k))).2
  rw [← homogeneousFrequencyEmbedding_norm_sq_integral a k ha ha1 hk,
    Real.sqrt_sq (norm_nonneg _)] at h
  exact h

theorem homogeneousSchwartzConvolution_norm_le (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ φ : 𝓢(E, ℂ)) :
    ‖homogeneousFrequencyEmbedding a k ha ha1 hk (homogeneousSchwartzConvolution ψ φ)‖ ≤
      homogeneousAlgebraConstant a k *
        ‖homogeneousFrequencyEmbedding a k ha ha1 hk ψ‖ *
        ‖homogeneousFrequencyEmbedding a k ha ha1 hk φ‖ := by
  let c : ℝ := ((2 * Real.pi) ^ (12 : ℕ))⁻¹
  let C : ℝ := max (2 ^ (6 - a)) (2 ^ k)
  let D : ℝ := Real.sqrt (∫ ξ : E, (homogeneousFourierWeight a k ξ)⁻¹)
  let A : ℝ := ‖homogeneousFrequencyEmbedding a k ha ha1 hk ψ‖
  let B : ℝ := ‖homogeneousFrequencyEmbedding a k ha ha1 hk φ‖
  let Lψ : ℝ := ∫ ξ, ‖ψ ξ‖
  let Lφ : ℝ := ∫ ξ, ‖φ ξ‖
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have hLψ : 0 ≤ Lψ := integral_nonneg (fun _ => norm_nonneg _)
  have hLφ : 0 ≤ Lφ := integral_nonneg (fun _ => norm_nonneg _)
  have hψ := homogeneousFrequencyEmbedding_L1 a k ha ha1 hk ψ
  have hφ := homogeneousFrequencyEmbedding_L1 a k ha ha1 hk φ
  have hψsq : Lψ ^ 2 ≤ D ^ 2 * A ^ 2 := by
    simpa only [mul_pow] using (sq_le_sq₀ hLψ (mul_nonneg hD hA)).mpr hψ
  have hφsq : Lφ ^ 2 ≤ D ^ 2 * B ^ 2 := by
    simpa only [mul_pow] using (sq_le_sq₀ hLφ (mul_nonneg hD hB)).mpr hφ
  have hE (s : ℝ) (hs : 0 ≤ s) (hsC : 2 ^ s ≤ C) :
      homogeneousFrequencyEnergy s (homogeneousSchwartzConvolution ψ φ) ≤
        2 * C ^ 2 * (Lφ ^ 2 * homogeneousFrequencyEnergy s ψ +
          Lψ ^ 2 * homogeneousFrequencyEnergy s φ) := by
    apply (homogeneousSchwartzConvolution_energy_le s hs ψ φ).trans
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (by positivity) hC).mpr hsC) (by norm_num)
    · exact add_nonneg
        (mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => by positivity)))
        (mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => by positivity)))
  have hlow := hE (6 - a) (by linarith) (le_max_left _ _)
  have hhigh := hE k (by linarith) (le_max_right _ _)
  have hnψ := homogeneousFrequencyEmbedding_norm_sq a k ha ha1 hk ψ
  have hnφ := homogeneousFrequencyEmbedding_norm_sq a k ha ha1 hk φ
  have hsq :
      ‖homogeneousFrequencyEmbedding a k ha ha1 hk (homogeneousSchwartzConvolution ψ φ)‖ ^ 2 ≤
        (2 * C * D * A * B) ^ 2 := by
    calc
      _ = c * (homogeneousFrequencyEnergy (6 - a) (homogeneousSchwartzConvolution ψ φ) +
          homogeneousFrequencyEnergy k (homogeneousSchwartzConvolution ψ φ)) :=
        homogeneousFrequencyEmbedding_norm_sq a k ha ha1 hk _
      _ ≤ c * (2 * C ^ 2 * (Lφ ^ 2 * homogeneousFrequencyEnergy (6 - a) ψ +
          Lψ ^ 2 * homogeneousFrequencyEnergy (6 - a) φ) +
          2 * C ^ 2 * (Lφ ^ 2 * homogeneousFrequencyEnergy k ψ +
          Lψ ^ 2 * homogeneousFrequencyEnergy k φ)) :=
        mul_le_mul_of_nonneg_left (add_le_add hlow hhigh) hc
      _ = 2 * C ^ 2 * (Lφ ^ 2 * (c * (homogeneousFrequencyEnergy (6 - a) ψ +
          homogeneousFrequencyEnergy k ψ)) + Lψ ^ 2 *
          (c * (homogeneousFrequencyEnergy (6 - a) φ + homogeneousFrequencyEnergy k φ))) := by ring
      _ = 2 * C ^ 2 * (Lφ ^ 2 * A ^ 2 + Lψ ^ 2 * B ^ 2) := by
        rw [← hnψ, ← hnφ]
      _ ≤ 2 * C ^ 2 * ((D ^ 2 * B ^ 2) * A ^ 2 + (D ^ 2 * A ^ 2) * B ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_right hφsq (sq_nonneg _))
          (mul_le_mul_of_nonneg_right hψsq (sq_nonneg _))) (by positivity)
      _ = _ := by ring
  change ‖homogeneousFrequencyEmbedding a k ha ha1 hk (homogeneousSchwartzConvolution ψ φ)‖ ≤
    2 * C * D * A * B
  have hright : 0 ≤ 2 * C * D * A * B := by positivity
  exact (sq_le_sq₀ (norm_nonneg _) hright).mp hsq

end DefocusingNLS

end OAI
