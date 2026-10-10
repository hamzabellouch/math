import OAI.NumberTheory.JointDickman.Probability.ProjectedHistogramError
import OAI.NumberTheory.JointDickman.Probability.SampledHistogram
import OAI.NumberTheory.JointDickman.Probability.OppositeResidueProduct

namespace OAI

/-! # The two endpoint errors with the actual opposite Fourier frequencies -/

namespace JointDickman
open Finset MeasureTheory

theorem manuscript_histogram_opposite_product_error {m B q : ℕ} [NeZero q]
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
    ‖∑ h : ZMod q, if P h then
      manuscriptFourier m B q J₁ g₁ F₁ h*manuscriptFourier m B q J₂ g₂ F₂ (-h)-
      manuscriptApproxFourier m B q J₁ g₁ F₁ h*manuscriptApproxFourier m B q J₂ g₂ F₂ (-h) else 0‖ ≤
      Real.sqrt (manuscriptAmplitudeEnergy m B q J₁)*Real.sqrt (manuscriptAmplitudeEnergy m B q J₂)*
        channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂) := by
  obtain ⟨_,hc₁,he₁⟩ := manuscriptFourier_square_bounds (q := q) hm hB J₁ g₁ hg₁ F₁ hM₁ hL₁ hF₁ hI₁ hLip₁
  obtain ⟨ha₂,_,he₂⟩ := manuscriptFourier_square_bounds (q := q) hm hB J₂ g₂ hg₂ F₂ hM₂ hL₂ hF₂ hI₂ hLip₂
  have hh := restricted_opposite_residue_product_error_bound P _ _ _ _ he₁ he₂ hc₁ ha₂
  have hδ := (channelMesh_pos (channelFineCount_pos hm hB)).le
  rw [Real.sqrt_mul (manuscriptAmplitudeEnergy_nonneg hm hB J₁),
    Real.sqrt_mul (manuscriptAmplitudeEnergy_nonneg hm hB J₂),
    Real.sqrt_mul (manuscriptAmplitudeEnergy_nonneg hm hB J₁),
    Real.sqrt_mul (manuscriptAmplitudeEnergy_nonneg hm hB J₂),
    Real.sqrt_sq (mul_nonneg hL₁ hδ),Real.sqrt_sq (mul_nonneg hL₂ hδ),
    Real.sqrt_sq hM₁,Real.sqrt_sq hM₂] at hh
  exact hh.trans_eq (by ring)


theorem manuscriptHistogram_projection_opposite_error {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J₁ J₂ : Finset (Fin (channelFineCount m B)))
    (g₁ g₂ : (auxiliaryPrimes B → Bool) → ℝ)
    (hg₁ : ∀ x, |g₁ x| ≤ 1) (hg₂ : ∀ x, |g₂ x| ≤ 1)
    (F₁ F₂ : ℝ → ℂ) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hF₁ : ∀ i ∈ J₁, ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i), ‖F₁ x‖ ≤ M₁)
    (hF₂ : ∀ i ∈ J₂, ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i), ‖F₂ x‖ ≤ M₂)
    (P : ZMod q → Prop) [DecidablePred P] :
    ‖∑ h : ZMod q, if P h then
      manuscriptApproxFourier m B q J₁ g₁ F₁ h*manuscriptApproxFourier m B q J₂ g₂ F₂ (-h)-
      manuscriptProjectedFourier m B q J₁ g₁ F₁ h*manuscriptProjectedFourier m B q J₂ g₂ F₂ (-h) else 0‖ ≤
      M₁*M₂*(Real.sqrt (manuscriptResidueEnergy m B q J₁ g₁)*Real.sqrt (manuscriptAmplitudeEnergy m B q J₂)+
        Real.sqrt (manuscriptAmplitudeEnergy m B q J₁)*Real.sqrt (manuscriptResidueEnergy m B q J₂ g₂)) := by
  have he₁ := manuscriptHistogram_projection_square (q := q) hm hB J₁ g₁ F₁ hM₁ hF₁
  have he₂ := manuscriptHistogram_projection_square (q := q) hm hB J₂ g₂ F₂ hM₂ hF₂
  have ha₁ := (manuscript_amplitude_fourier_bounds (q := q) hm hB J₁ g₁ hg₁ F₁ hM₁ hF₁).2
  have ha₂ := (manuscript_amplitude_fourier_bounds (q := q) hm hB J₂ g₂ hg₂ F₂ hM₂ hF₂).2
  have hp₁ := (manuscriptProjectedFourier_square_le m B q J₁ g₁ F₁).trans ha₁
  have hr₁ : (∑ h : ZMod q, ‖manuscriptProjectedFourier m B q J₁ g₁ F₁ h‖^2) ≤
      manuscriptAmplitudeEnergy m B q J₁*M₁^2 := hp₁.trans_eq (by unfold manuscriptAmplitudeEnergy; ring)
  have hr₂ : (∑ h : ZMod q, ‖manuscriptApproxFourier m B q J₂ g₂ F₂ h‖^2) ≤
      manuscriptAmplitudeEnergy m B q J₂*M₂^2 := ha₂.trans_eq (by unfold manuscriptAmplitudeEnergy; ring)
  have hh := restricted_opposite_residue_product_error_bound P _ _ _ _ he₁ he₂ hr₁ hr₂
  rw [Real.sqrt_mul (manuscriptResidueEnergy_nonneg hm hB J₁ g₁),
    Real.sqrt_mul (manuscriptResidueEnergy_nonneg hm hB J₂ g₂),
    Real.sqrt_mul (manuscriptAmplitudeEnergy_nonneg hm hB J₁),
    Real.sqrt_mul (manuscriptAmplitudeEnergy_nonneg hm hB J₂),
    Real.sqrt_sq hM₁,Real.sqrt_sq hM₂] at hh
  exact hh.trans_eq (by ring)


theorem projected_histogram_sampled_opposite_error {m B q : ℕ} [NeZero q]
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
    ‖∑ h : ZMod q, if P h then
      manuscriptProjectedFourier m B q J₁ g₁ F₁ h*manuscriptProjectedFourier m B q J₂ g₂ F₂ (-h)-
      sampledProjectedFourier m B q J₁ g₁ (fun i => F₁ (channelLower (channelFineCount m B) i)) h*sampledProjectedFourier m B q J₂ g₂ (fun i => F₂ (channelLower (channelFineCount m B) i)) (-h) else 0‖ ≤
      Real.sqrt (manuscriptAmplitudeEnergy m B q J₁)*Real.sqrt (manuscriptAmplitudeEnergy m B q J₂)*
        channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂) := by
  have he₁ := projected_averaged_to_sampled_square_error (q := q) hm hB J₁ g₁ hg₁ F₁ hL₁ hI₁ hLip₁
  have he₂ := projected_averaged_to_sampled_square_error (q := q) hm hB J₂ g₂ hg₂ F₂ hL₂ hI₂ hLip₂
  have hlow (i : Fin (channelFineCount m B)) : channelLower (channelFineCount m B) i ∈
      Set.Icc (channelLower (channelFineCount m B) i) (channelUpper (channelFineCount m B) i) := by
    refine ⟨le_rfl,?_⟩
    linarith [channel_width (channelFineCount m B) i,
      channelMesh_pos (channelFineCount_pos hm hB)]
  have hs₁ := sampledProjectedFourier_square_le (q := q) hm hB J₁ g₁ hg₁
    (fun i => F₁ (channelLower (channelFineCount m B) i)) hM₁
    (fun i hi => hF₁ i hi _ (hlow i))
  have ha₂ := (manuscriptFourier_square_bounds (q := q) hm hB J₂ g₂ hg₂ F₂
    hM₂ hL₂ hF₂ hI₂ hLip₂).2.1
  have hp₂ := (manuscriptProjectedFourier_square_le m B q J₂ g₂ F₂).trans ha₂
  have hh := restricted_opposite_residue_product_error_bound P _ _ _ _ he₁ he₂ hs₁ hp₂
  have hδ := (channelMesh_pos (channelFineCount_pos hm hB)).le
  rw [Real.sqrt_mul (manuscriptAmplitudeEnergy_nonneg hm hB J₁),
    Real.sqrt_mul (manuscriptAmplitudeEnergy_nonneg hm hB J₂),
    Real.sqrt_mul (manuscriptAmplitudeEnergy_nonneg hm hB J₁),
    Real.sqrt_mul (manuscriptAmplitudeEnergy_nonneg hm hB J₂),
    Real.sqrt_sq (mul_nonneg hL₁ hδ),Real.sqrt_sq (mul_nonneg hL₂ hδ),
    Real.sqrt_sq hM₁,Real.sqrt_sq hM₂] at hh
  exact hh.trans_eq (by ring)

end JointDickman

end OAI
