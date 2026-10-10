import OAI.NumberTheory.JointDickman.Probability.ProjectedHistogramError

namespace OAI

/-! # Integrating the actual histogram residue projection -/

namespace JointDickman
open Finset MeasureTheory

theorem manuscriptHistogram_projection_integral_error {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J₁ J₂ : Finset (Fin (channelFineCount m B)))
    (g₁ g₂ : (auxiliaryPrimes B → Bool) → ℝ)
    (hg₁ : ∀ x, |g₁ x| ≤ 1) (hg₂ : ∀ x, |g₂ x| ≤ 1)
    (F₁ F₂ : ℝ → ℝ → ℂ) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hF₁ : ∀ ξ, ∀ i ∈ J₁, ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i), ‖F₁ ξ x‖ ≤ M₁)
    (hF₂ : ∀ ξ, ∀ i ∈ J₂, ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i), ‖F₂ ξ x‖ ≤ M₂)
    (P : ZMod q → Prop) [DecidablePred P]
    {l u : ℝ} (hlu : l ≤ u) (W : ℝ → ℂ) (hW : Continuous W) :
    ‖∫ ξ in l..u, W ξ*(∑ h : ZMod q, if P h then
      manuscriptApproxFourier m B q J₁ g₁ (F₁ ξ) h*manuscriptApproxFourier m B q J₂ g₂ (F₂ ξ) h-
      manuscriptProjectedFourier m B q J₁ g₁ (F₁ ξ) h*manuscriptProjectedFourier m B q J₂ g₂ (F₂ ξ) h else 0)‖ ≤
      M₁*M₂*(Real.sqrt (manuscriptResidueEnergy m B q J₁ g₁)*Real.sqrt (manuscriptAmplitudeEnergy m B q J₂)+
        Real.sqrt (manuscriptAmplitudeEnergy m B q J₁)*Real.sqrt (manuscriptResidueEnergy m B q J₂ g₂))*(∫ ξ in l..u, ‖W ξ‖) := by
  let C := M₁*M₂*(Real.sqrt (manuscriptResidueEnergy m B q J₁ g₁)*Real.sqrt (manuscriptAmplitudeEnergy m B q J₂)+
    Real.sqrt (manuscriptAmplitudeEnergy m B q J₁)*Real.sqrt (manuscriptResidueEnergy m B q J₂ g₂))
  have he (ξ : ℝ) :
      ‖∑ h : ZMod q, if P h then
        manuscriptApproxFourier m B q J₁ g₁ (F₁ ξ) h*manuscriptApproxFourier m B q J₂ g₂ (F₂ ξ) h-
        manuscriptProjectedFourier m B q J₁ g₁ (F₁ ξ) h*manuscriptProjectedFourier m B q J₂ g₂ (F₂ ξ) h
        else 0‖ ≤ C :=
    manuscriptHistogram_projection_product_error hm hB J₁ J₂ g₁ g₂ hg₁ hg₂
      (F₁ ξ) (F₂ ξ) hM₁ hM₂ (hF₁ ξ) (hF₂ ξ) P
  calc
    _ ≤ ∫ ξ in l..u, C*‖W ξ‖ := intervalIntegral.norm_integral_le_of_norm_le hlu
      (Filter.Eventually.of_forall (fun ξ _ => by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left (he ξ) (norm_nonneg _)).trans_eq (mul_comm _ _)))
      ((continuous_const.mul hW.norm).intervalIntegrable l u)
    _ = _ := intervalIntegral.integral_const_mul _ _

end JointDickman

end OAI
