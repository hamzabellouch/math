import OAI.NumberTheory.JointDickman.Probability.SampledHistogramError
import OAI.NumberTheory.JointDickman.Amplification.FourierProfileTail

namespace OAI

/-! # The full-line Fourier error from actual endpoint sums to sampled logarithmic masses -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap

theorem schwartz_weighted_linear_error (w : 𝓢(ℝ,ℝ)) (H : ℝ → ℂ)
    {A D : ℝ} (hD : 0 ≤ D) (hH : ∀ ξ, ‖H ξ‖ ≤ A*(1+|ξ|)+D) :
    ‖∫ ξ : ℝ, testFourierTransform w ξ*H ξ‖ ≤
      (A+D)*(∫ ξ : ℝ, ‖testFourierTransform w ξ‖*(1+|ξ|)) := by
  calc
    _ ≤ ∫ ξ : ℝ, (A+D)*(‖testFourierTransform w ξ‖*(1+|ξ|)) := by
      apply norm_integral_le_of_norm_le ((schwartz_testFourier_linear_moment w).const_mul (A+D))
      filter_upwards [] with ξ
      rw [norm_mul]
      have he : A*(1+|ξ|)+D ≤ (A+D)*(1+|ξ|) := by
        nlinarith [mul_nonneg hD (abs_nonneg ξ)]
      exact (mul_le_mul_of_nonneg_left ((hH ξ).trans he) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

theorem manuscript_to_sampled_integral_error {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J₁ J₂ : Finset (Fin (channelFineCount m B)))
    (g₁ g₂ : (auxiliaryPrimes B → Bool) → ℝ)
    (hg₁ : ∀ x, |g₁ x| ≤ 1) (hg₂ : ∀ x, |g₂ x| ≤ 1)
    (F₁ F₂ : ℝ → ℝ → ℂ) {M₁ M₂ L₁ L₂ : ℝ}
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hF₁ : ∀ ξ, ∀ i ∈ J₁, ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i), ‖F₁ ξ x‖ ≤ M₁)
    (hF₂ : ∀ ξ, ∀ i ∈ J₂, ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i), ‖F₂ ξ x‖ ≤ M₂)
    (hI₁ : ∀ ξ, ∀ i ∈ J₁, IntervalIntegrable (F₁ ξ) volume
      (channelLower (channelFineCount m B) i) (channelUpper (channelFineCount m B) i))
    (hI₂ : ∀ ξ, ∀ i ∈ J₂, IntervalIntegrable (F₂ ξ) volume
      (channelLower (channelFineCount m B) i) (channelUpper (channelFineCount m B) i))
    (hLip₁ : ∀ ξ, ∀ i ∈ J₁, ∀ u ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i),
      ∀ v ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i), ‖F₁ ξ u-F₁ ξ v‖ ≤ (L₁*(1+|ξ|))*|u-v|)
    (hLip₂ : ∀ ξ, ∀ i ∈ J₂, ∀ u ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i),
      ∀ v ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i), ‖F₂ ξ u-F₂ ξ v‖ ≤ (L₂*(1+|ξ|))*|u-v|)
    (P : ZMod q → Prop) [DecidablePred P] (w : 𝓢(ℝ,ℝ)) :
    ‖∫ ξ : ℝ, testFourierTransform w ξ*
      (oppositeProductSum P (manuscriptFourier m B q J₁ g₁ (F₁ ξ))
          (manuscriptFourier m B q J₂ g₂ (F₂ ξ))-
        oppositeProductSum P
          (sampledProjectedFourier m B q J₁ g₁ (fun i => F₁ ξ (channelLower (channelFineCount m B) i)))
          (sampledProjectedFourier m B q J₂ g₂ (fun i => F₂ ξ (channelLower (channelFineCount m B) i))))‖ ≤
      (2*Real.sqrt (manuscriptAmplitudeEnergy m B q J₁)*Real.sqrt (manuscriptAmplitudeEnergy m B q J₂)*
          channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂)+
        M₁*M₂*(Real.sqrt (manuscriptResidueEnergy m B q J₁ g₁)*Real.sqrt (manuscriptAmplitudeEnergy m B q J₂)+
          Real.sqrt (manuscriptAmplitudeEnergy m B q J₁)*Real.sqrt (manuscriptResidueEnergy m B q J₂ g₂)))*
        (∫ ξ : ℝ, ‖testFourierTransform w ξ‖*(1+|ξ|)) := by
  apply schwartz_weighted_linear_error w
  · positivity
  · intro ξ
    have hh := manuscript_to_sampled_product_error hm hB J₁ J₂ g₁ g₂ hg₁ hg₂ (F₁ ξ) (F₂ ξ)
      hM₁ hM₂ (mul_nonneg hL₁ (by positivity)) (mul_nonneg hL₂ (by positivity))
      (hF₁ ξ) (hF₂ ξ) (hI₁ ξ) (hI₂ ξ) (hLip₁ ξ) (hLip₂ ξ) P
    exact hh.trans_eq (by ring)

end JointDickman

end OAI
