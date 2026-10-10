import OAI.NumberTheory.JointDickman.Probability.HistogramProductError

namespace OAI

/-! # Integrated error for the actual endpoint histogram product -/

namespace JointDickman
open Finset MeasureTheory

theorem manuscript_histogram_integral_error {m B q : ℕ} [NeZero q]
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
    (P : ZMod q → Prop) [DecidablePred P]
    {l u : ℝ} (hlu : l ≤ u) (W : ℝ → ℂ) (hW : Continuous W) :
    ‖∫ ξ in l..u, W ξ*(∑ h : ZMod q, if P h then
      manuscriptFourier m B q J₁ g₁ (F₁ ξ) h*manuscriptFourier m B q J₂ g₂ (F₂ ξ) h-
      manuscriptApproxFourier m B q J₁ g₁ (F₁ ξ) h*manuscriptApproxFourier m B q J₂ g₂ (F₂ ξ) h else 0)‖ ≤
      Real.sqrt (manuscriptAmplitudeEnergy m B q J₁)*Real.sqrt (manuscriptAmplitudeEnergy m B q J₂)*
        channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂)*(∫ ξ in l..u, ‖W ξ‖*(1+|ξ|)) := by
  let C := Real.sqrt (manuscriptAmplitudeEnergy m B q J₁)*
    Real.sqrt (manuscriptAmplitudeEnergy m B q J₂)*channelMesh (channelFineCount m B)*
      (L₁*M₂+M₁*L₂)
  have hV : Continuous (fun ξ : ℝ => C*(‖W ξ‖*(1+|ξ|))) :=
    continuous_const.mul (hW.norm.mul (continuous_const.add continuous_abs))
  have he (ξ : ℝ) :
      ‖∑ h : ZMod q, if P h then
        manuscriptFourier m B q J₁ g₁ (F₁ ξ) h*manuscriptFourier m B q J₂ g₂ (F₂ ξ) h-
        manuscriptApproxFourier m B q J₁ g₁ (F₁ ξ) h*manuscriptApproxFourier m B q J₂ g₂ (F₂ ξ) h
        else 0‖ ≤ C*(1+|ξ|) := by
    have hh := manuscript_histogram_product_error hm hB J₁ J₂ g₁ g₂ hg₁ hg₂ (F₁ ξ) (F₂ ξ)
      hM₁ hM₂ (mul_nonneg hL₁ (by positivity)) (mul_nonneg hL₂ (by positivity))
      (hF₁ ξ) (hF₂ ξ) (hI₁ ξ) (hI₂ ξ) (hLip₁ ξ) (hLip₂ ξ) P
    exact hh.trans_eq (by dsimp [C]; ring)
  calc
    _ ≤ ∫ ξ in l..u, C*(‖W ξ‖*(1+|ξ|)) :=
      intervalIntegral.norm_integral_le_of_norm_le hlu
        (Filter.Eventually.of_forall (fun ξ _ => by
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_left (he ξ) (norm_nonneg _)).trans_eq (by ring)))
        (hV.intervalIntegrable l u)
    _ = _ := intervalIntegral.integral_const_mul _ _

end JointDickman

end OAI
