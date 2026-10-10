import OAI.MathematicalPhysics.DefocusingNLS.Linear.ContinuousYoung
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeFourier

namespace OAI

/-! # Exact homogeneous weights for continuous Fourier convolution -/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousFourierMagnitude (s : ℝ) (ψ : 𝓢(E, ℂ)) (ξ : E) : ℝ :=
  ‖ξ‖ ^ s * ‖ψ ξ‖

theorem homogeneousFourierMagnitude_nonneg (s : ℝ) (ψ : 𝓢(E, ℂ)) (ξ : E) :
    0 ≤ homogeneousFourierMagnitude s ψ ξ :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)

theorem homogeneousFourierMagnitude_continuous (s : ℝ) (hs : 0 ≤ s) (ψ : 𝓢(E, ℂ)) :
    Continuous (homogeneousFourierMagnitude s ψ) :=
  (continuous_norm.rpow_const (fun _ => Or.inr hs)).mul ψ.continuous.norm

private theorem homogeneous_magnitude_le_bessel (s : ℝ) (hs : 0 ≤ s)
    (ψ : 𝓢(E, ℂ)) (ξ : E) :
    homogeneousFourierMagnitude s ψ ξ ≤ ‖weightedSchwartzKernel s ψ ξ‖ := by
  have hw : ‖ξ‖ ^ s ≤ (1 + ‖ξ‖ ^ 2) ^ (s / 2) := by
    calc
      _ = (‖ξ‖ ^ (2 : ℕ)) ^ (s / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  rw [weightedSchwartzKernel_norm]
  exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)

theorem homogeneousFourierMagnitude_integrable (s : ℝ) (hs : 0 ≤ s) (ψ : 𝓢(E, ℂ)) :
    Integrable (homogeneousFourierMagnitude s ψ) := by
  apply (weightedSchwartzKernel s ψ).integrable.norm.mono'
    (homogeneousFourierMagnitude_continuous s hs ψ).aestronglyMeasurable
  exact ae_of_all _ (fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (homogeneousFourierMagnitude_nonneg s ψ ξ)]
    exact homogeneous_magnitude_le_bessel s hs ψ ξ)

theorem homogeneousFourierMagnitude_bounded (s : ℝ) (hs : 0 ≤ s) (ψ : 𝓢(E, ℂ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ξ, homogeneousFourierMagnitude s ψ ξ ≤ K := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 (weightedSchwartzKernel s ψ), by positivity, fun ξ => ?_⟩
  exact (homogeneous_magnitude_le_bessel s hs ψ ξ).trans
    (SchwartzMap.norm_le_seminorm ℝ (weightedSchwartzKernel s ψ) ξ)

theorem homogeneousFourierMagnitude_sq_integrable (s : ℝ) (hs : 0 ≤ s)
    (ψ : 𝓢(E, ℂ)) : Integrable (fun ξ => homogeneousFourierMagnitude s ψ ξ ^ 2) := by
  obtain ⟨χ, hχ⟩ := radianFourierKernel_surjective ψ
  have h := integrable_localizedFourierPolynomial_energy s 1 hs zero_lt_one χ {0} (fun _ => 1)
  have heq : localizedFourierPolynomial 1 χ {0} (fun _ => 1) = (χ : E → ℂ) := by
    funext y
    simp [localizedFourierPolynomial]
  rw [heq] at h
  have he (ξ : E) : homogeneousFourierMagnitude s ψ ξ ^ 2 =
      ‖ξ‖ ^ (2 * s) * ‖radianFourierIntegral χ ξ‖ ^ 2 := by
    rw [homogeneousFourierMagnitude, mul_pow, ← hχ, radianFourierKernel_apply,
      ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 2
    ring
  simpa only [he] using h

/-- A sum of frequencies costs only the fixed constant `2^s`. -/
theorem homogeneousFrequencyWeight_add_le (s : ℝ) (hs : 0 ≤ s) (ξ η : E) :
    ‖ξ + η‖ ^ s ≤ 2 ^ s * (‖ξ‖ ^ s + ‖η‖ ^ s) := by
  have hn : ‖ξ + η‖ ≤ 2 * max ‖ξ‖ ‖η‖ :=
    (norm_add_le _ _).trans (by linarith [le_max_left ‖ξ‖ ‖η‖, le_max_right ‖ξ‖ ‖η‖])
  calc
    _ ≤ (2 * max ‖ξ‖ ‖η‖) ^ s := Real.rpow_le_rpow (norm_nonneg _) hn hs
    _ = 2 ^ s * max (‖ξ‖ ^ s) (‖η‖ ^ s) := by
      rw [Real.mul_rpow (by norm_num) (by positivity),
        Real.rpow_max (norm_nonneg _) (norm_nonneg _) hs]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (max_le (le_add_of_nonneg_right (by positivity))
        (le_add_of_nonneg_left (by positivity))) (by positivity)

end DefocusingNLS

end OAI
