import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousConvolutionWeights
import Mathlib.Analysis.Fourier.Convolution

namespace OAI

/-! # Weighted continuous-frequency convolution on the Schwartz core of Y -/

open MeasureTheory
open scoped SchwartzMap Convolution

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousSchwartzConvolution (ψ φ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) ψ φ

private theorem positive_integrand_integrable (f g : E → ℝ)
    (hf : Integrable f) (hg : Continuous g) (hgp : ∀ ξ, 0 ≤ g ξ)
    (K : ℝ) (hK : ∀ ξ, g ξ ≤ K) (ξ : E) :
    Integrable (fun η => f η * g (ξ - η)) := by
  apply hf.mul_bdd (c := K) (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact ae_of_all _ (fun η => by
    change ‖g (ξ - η)‖ ≤ K
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hgp _)] using hK (ξ - η))

theorem homogeneousSchwartzConvolution_weighted_pointwise (s : ℝ) (hs : 0 ≤ s)
    (ψ φ : 𝓢(E, ℂ)) (ξ : E) :
    homogeneousFourierMagnitude s (homogeneousSchwartzConvolution ψ φ) ξ ≤
      2 ^ s * (positiveFrequencyConvolution (fun η => ‖φ η‖)
        (homogeneousFourierMagnitude s ψ) ξ +
      positiveFrequencyConvolution (fun η => ‖ψ η‖)
        (homogeneousFourierMagnitude s φ) ξ) := by
  obtain ⟨Kφ, _, hKφ⟩ := homogeneousFourierMagnitude_bounded s hs φ
  have hI₁ : Integrable (fun η => homogeneousFourierMagnitude s ψ η * ‖φ (ξ - η)‖) :=
    positive_integrand_integrable _ _ (homogeneousFourierMagnitude_integrable s hs ψ)
      φ.continuous.norm (fun _ => norm_nonneg _) (SchwartzMap.seminorm ℝ 0 0 φ)
      (SchwartzMap.norm_le_seminorm ℝ φ) ξ
  have hI₂ : Integrable (fun η => ‖ψ η‖ * homogeneousFourierMagnitude s φ (ξ - η)) :=
    positive_integrand_integrable _ _ ψ.integrable.norm
      (homogeneousFourierMagnitude_continuous s hs φ)
      (homogeneousFourierMagnitude_nonneg s φ) Kφ hKφ ξ
  have hpoint (η : E) :
      ‖ξ‖ ^ s * (‖ψ η‖ * ‖φ (ξ - η)‖) ≤
      2 ^ s * (homogeneousFourierMagnitude s ψ η * ‖φ (ξ - η)‖ +
        ‖ψ η‖ * homogeneousFourierMagnitude s φ (ξ - η)) := by
    have hw := homogeneousFrequencyWeight_add_le s hs η (ξ - η)
    rw [add_sub_cancel] at hw
    have hm := mul_le_mul_of_nonneg_right hw (mul_nonneg (norm_nonneg (ψ η))
      (norm_nonneg (φ (ξ - η))))
    dsimp only [homogeneousFourierMagnitude]
    convert hm using 1; ring
  have hi : (∫ η, ‖ξ‖ ^ s * (‖ψ η‖ * ‖φ (ξ - η)‖)) ≤
      ∫ η, 2 ^ s * (homogeneousFourierMagnitude s ψ η * ‖φ (ξ - η)‖ +
        ‖ψ η‖ * homogeneousFourierMagnitude s φ (ξ - η)) :=
    integral_mono_of_nonneg
      (ae_of_all _ (fun η => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))))
      ((hI₁.add hI₂).const_mul _) (ae_of_all _ hpoint)
  calc
    _ ≤ ‖ξ‖ ^ s * ∫ η, ‖ψ η‖ * ‖φ (ξ - η)‖ := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) _)
      change ‖SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) ψ φ ξ‖ ≤ _
      rw [SchwartzMap.convolution_apply]
      change ‖∫ η, ψ η * φ (ξ - η)‖ ≤ _
      simpa only [norm_mul] using
        (norm_integral_le_integral_norm (fun η => ψ η * φ (ξ - η)))
    _ = (∫ η, ‖ξ‖ ^ s * (‖ψ η‖ * ‖φ (ξ - η)‖)) := (integral_const_mul _ _).symm
    _ ≤ _ := hi
    _ = _ := by
      rw [integral_const_mul, integral_add hI₁ hI₂]
      change 2 ^ s * (positiveFrequencyConvolution (homogeneousFourierMagnitude s ψ)
        (fun η => ‖φ η‖) ξ + _) = _
      rw [positiveFrequencyConvolution_comm]
      rfl

/-- The homogeneous energy is controlled by the L¹ norms and matching energies. -/
theorem homogeneousSchwartzConvolution_energy_le (s : ℝ) (hs : 0 ≤ s)
    (ψ φ : 𝓢(E, ℂ)) :
    homogeneousFrequencyEnergy s (homogeneousSchwartzConvolution ψ φ) ≤
      2 * (2 ^ s) ^ 2 * ((∫ ξ, ‖φ ξ‖) ^ 2 * homogeneousFrequencyEnergy s ψ +
        (∫ ξ, ‖ψ ξ‖) ^ 2 * homogeneousFrequencyEnergy s φ) := by
  obtain ⟨Kψ, hKψ, hψ⟩ := homogeneousFourierMagnitude_bounded s hs ψ
  obtain ⟨Kφ, hKφ, hφ⟩ := homogeneousFourierMagnitude_bounded s hs φ
  have hY₁ := continuousYoung_nonnegative (fun ξ => ‖φ ξ‖)
    (homogeneousFourierMagnitude s ψ) φ.integrable.norm
    (homogeneousFourierMagnitude_continuous s hs ψ) (fun _ => norm_nonneg _)
    (homogeneousFourierMagnitude_nonneg s ψ)
    (homogeneousFourierMagnitude_sq_integrable s hs ψ) Kψ hKψ hψ
  have hY₂ := continuousYoung_nonnegative (fun ξ => ‖ψ ξ‖)
    (homogeneousFourierMagnitude s φ) ψ.integrable.norm
    (homogeneousFourierMagnitude_continuous s hs φ) (fun _ => norm_nonneg _)
    (homogeneousFourierMagnitude_nonneg s φ)
    (homogeneousFourierMagnitude_sq_integrable s hs φ) Kφ hKφ hφ
  let U := positiveFrequencyConvolution (fun ξ => ‖φ ξ‖) (homogeneousFourierMagnitude s ψ)
  let V := positiveFrequencyConvolution (fun ξ => ‖ψ ξ‖) (homogeneousFourierMagnitude s φ)
  have hpoint (ξ : E) :
      homogeneousFourierMagnitude s (homogeneousSchwartzConvolution ψ φ) ξ ^ 2 ≤
      2 * (2 ^ s) ^ 2 * (U ξ ^ 2 + V ξ ^ 2) := by
    have hU : 0 ≤ U ξ := integral_nonneg (fun η =>
      mul_nonneg (norm_nonneg _) (homogeneousFourierMagnitude_nonneg s ψ _))
    have hV : 0 ≤ V ξ := integral_nonneg (fun η =>
      mul_nonneg (norm_nonneg _) (homogeneousFourierMagnitude_nonneg s φ _))
    have hm := homogeneousSchwartzConvolution_weighted_pointwise s hs ψ φ ξ
    have hsquare := pow_le_pow_left₀
      (homogeneousFourierMagnitude_nonneg s (homogeneousSchwartzConvolution ψ φ) ξ) hm 2
    change _ ≤ (2 ^ s * (U ξ + V ξ)) ^ 2 at hsquare
    exact hsquare.trans (by
      nlinarith [mul_nonneg (sq_nonneg (2 ^ s)) (sq_nonneg (U ξ - V ξ))])
  have hI := integral_mono
    (homogeneousFourierMagnitude_sq_integrable s hs (homogeneousSchwartzConvolution ψ φ))
    ((hY₁.1.add hY₂.1).const_mul (2 * (2 ^ s) ^ 2)) hpoint
  rw [integral_const_mul] at hI
  simp only [Pi.add_apply] at hI
  rw [integral_add hY₁.1 hY₂.1] at hI
  have henergy (χ : 𝓢(E, ℂ)) :
      (∫ ξ, homogeneousFourierMagnitude s χ ξ ^ 2) = homogeneousFrequencyEnergy s χ := by
    change (∫ ξ, homogeneousFourierMagnitude s χ ξ ^ 2) =
      ∫ ξ, ‖ξ‖ ^ (2 * s) * ‖χ ξ‖ ^ 2
    apply integral_congr_ae
    filter_upwards [] with ξ
    rw [homogeneousFourierMagnitude, mul_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 2
    ring
  rw [henergy] at hI
  exact hI.trans ((mul_le_mul_of_nonneg_left (add_le_add hY₁.2 hY₂.2)
    (by positivity)).trans_eq (by rw [henergy, henergy]))

end DefocusingNLS

end OAI
