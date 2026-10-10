import OAI.NumberTheory.JointDickman.Probability.HistogramOppositeErrors

namespace OAI

/-! # Complete local error from actual endpoints to the sampled projected kernel -/

namespace JointDickman
open Finset MeasureTheory

noncomputable def oppositeProductSum {q : ℕ} [NeZero q] (P : ZMod q → Prop) [DecidablePred P]
    (A B : ZMod q → ℂ) : ℂ := ∑ h : ZMod q, if P h then A h*B (-h) else 0

theorem oppositeProductSum_sub {q : ℕ} [NeZero q] (P : ZMod q → Prop) [DecidablePred P]
    (A B C D : ZMod q → ℂ) :
    oppositeProductSum P A B-oppositeProductSum P C D =
      ∑ h : ZMod q, if P h then A h*B (-h)-C h*D (-h) else 0 := by
  unfold oppositeProductSum
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro h _
  split_ifs <;> simp

theorem manuscript_to_sampled_product_error {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J₁ J₂ : Finset (Fin (channelFineCount m B)))
    (g₁ g₂ : (auxiliaryPrimes B → Bool) → ℝ)
    (hg₁ : ∀ x, |g₁ x| ≤ 1) (hg₂ : ∀ x, |g₂ x| ≤ 1)
    (F₁ F₂ : ℝ → ℂ) {M₁ M₂ L₁ L₂ : ℝ}
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hF₁ : ∀ i ∈ J₁, ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i), ‖F₁ x‖ ≤ M₁)
    (hF₂ : ∀ i ∈ J₂, ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i), ‖F₂ x‖ ≤ M₂)
    (hI₁ : ∀ i ∈ J₁, IntervalIntegrable F₁ volume
      (channelLower (channelFineCount m B) i) (channelUpper (channelFineCount m B) i))
    (hI₂ : ∀ i ∈ J₂, IntervalIntegrable F₂ volume
      (channelLower (channelFineCount m B) i) (channelUpper (channelFineCount m B) i))
    (hLip₁ : ∀ i ∈ J₁, ∀ u ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i),
      ∀ v ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i), ‖F₁ u-F₁ v‖ ≤ L₁*|u-v|)
    (hLip₂ : ∀ i ∈ J₂, ∀ u ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i),
      ∀ v ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i), ‖F₂ u-F₂ v‖ ≤ L₂*|u-v|)
    (P : ZMod q → Prop) [DecidablePred P] :
    ‖oppositeProductSum P (manuscriptFourier m B q J₁ g₁ F₁)
        (manuscriptFourier m B q J₂ g₂ F₂)-
      oppositeProductSum P
        (sampledProjectedFourier m B q J₁ g₁ (fun i => F₁ (channelLower (channelFineCount m B) i)))
        (sampledProjectedFourier m B q J₂ g₂ (fun i => F₂ (channelLower (channelFineCount m B) i)))‖ ≤
      2*Real.sqrt (manuscriptAmplitudeEnergy m B q J₁)*Real.sqrt (manuscriptAmplitudeEnergy m B q J₂)*
        channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂)+
      M₁*M₂*(Real.sqrt (manuscriptResidueEnergy m B q J₁ g₁)*Real.sqrt (manuscriptAmplitudeEnergy m B q J₂)+
        Real.sqrt (manuscriptAmplitudeEnergy m B q J₁)*Real.sqrt (manuscriptResidueEnergy m B q J₂ g₂)) := by
  have he₀ := manuscript_histogram_opposite_product_error hm hB J₁ J₂ g₁ g₂ hg₁ hg₂
    F₁ F₂ hM₁ hM₂ hL₁ hL₂ hF₁ hF₂ hI₁ hI₂ hLip₁ hLip₂ P
  have he₁ := manuscriptHistogram_projection_opposite_error hm hB J₁ J₂ g₁ g₂ hg₁ hg₂
    F₁ F₂ hM₁ hM₂ hF₁ hF₂ P
  have he₂ := projected_histogram_sampled_opposite_error hm hB J₁ J₂ g₁ g₂ hg₁ hg₂
    F₁ F₂ hM₁ hM₂ hL₁ hL₂ hF₁ hF₂ hI₁ hI₂ hLip₁ hLip₂ P
  rw [← oppositeProductSum_sub] at he₀ he₁ he₂
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (oppositeProductSum P (manuscriptFourier m B q J₁ g₁ F₁) (manuscriptFourier m B q J₂ g₂ F₂))
    (oppositeProductSum P (manuscriptApproxFourier m B q J₁ g₁ F₁) (manuscriptApproxFourier m B q J₂ g₂ F₂))
    (oppositeProductSum P
      (sampledProjectedFourier m B q J₁ g₁ (fun i => F₁ (channelLower (channelFineCount m B) i)))
      (sampledProjectedFourier m B q J₂ g₂ (fun i => F₂ (channelLower (channelFineCount m B) i))))
  have hinner := norm_sub_le_norm_sub_add_norm_sub
    (oppositeProductSum P (manuscriptApproxFourier m B q J₁ g₁ F₁) (manuscriptApproxFourier m B q J₂ g₂ F₂))
    (oppositeProductSum P (manuscriptProjectedFourier m B q J₁ g₁ F₁) (manuscriptProjectedFourier m B q J₂ g₂ F₂))
    (oppositeProductSum P
      (sampledProjectedFourier m B q J₁ g₁ (fun i => F₁ (channelLower (channelFineCount m B) i)))
      (sampledProjectedFourier m B q J₂ g₂ (fun i => F₂ (channelLower (channelFineCount m B) i))))
  exact (htriangle.trans (add_le_add he₀ (hinner.trans (add_le_add he₁ he₂)))).trans_eq (by ring)

end JointDickman

end OAI
