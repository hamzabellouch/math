import OAI.NumberTheory.JointDickman.Probability.ProjectedHistogram
import OAI.NumberTheory.JointDickman.Probability.HistogramResidueProjection

namespace OAI

/-! # Local residue-projection errors of the actual endpoint histograms -/

namespace JointDickman
open Finset MeasureTheory

noncomputable def manuscriptResidueEnergy (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B))) (g : (auxiliaryPrimes B → Bool) → ℝ) : ℝ :=
  ((q : ℝ)/(q.totient : ℝ))*((J.card : ℝ)*channelMesh (channelFineCount m B))*
    (∑ i ∈ J, ∑ r : (ZMod q)ˣ, (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
      (manuscriptChannel m B q g (i,r)-finiteResidueAverage (fun s => manuscriptChannel m B q g (i,s)))^2)

theorem manuscriptResidueEnergy_nonneg {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) : 0 ≤ manuscriptResidueEnergy m B q J g := by
  have hδ := (channelMesh_pos (channelFineCount_pos hm hB)).le
  unfold manuscriptResidueEnergy
  positivity

theorem manuscriptHistogram_projection_square {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i ∈ J, ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i), ‖F x‖ ≤ M) :
    (∑ h : ZMod q, ‖manuscriptApproxFourier m B q J g F h-manuscriptProjectedFourier m B q J g F h‖^2) ≤
      manuscriptResidueEnergy m B q J g*M^2 := by
  have hFavg : ∀ i ∈ J, ‖complexCellAverage (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i) F‖ ≤ M := by
    intro i hi
    have hw := channel_width (channelFineCount m B) i
    apply complexCellAverage_norm_le _ (hF i hi)
    linarith [channelMesh_pos (channelFineCount_pos hm hB)]
  have hh := manuscript_histogram_residue_projection (q := q) hm hB J g
    (fun i => complexCellAverage (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i) F) hM hFavg
  simp_rw [← manuscriptHistogram_centered_identity] at hh
  exact hh.trans_eq (by unfold manuscriptResidueEnergy; ring)

theorem manuscriptHistogram_projection_product_error {m B q : ℕ} [NeZero q]
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
      manuscriptApproxFourier m B q J₁ g₁ F₁ h*manuscriptApproxFourier m B q J₂ g₂ F₂ h-
      manuscriptProjectedFourier m B q J₁ g₁ F₁ h*manuscriptProjectedFourier m B q J₂ g₂ F₂ h else 0‖ ≤
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
  have hh := restricted_residue_product_error_bound P _ _ _ _ he₁ he₂ hr₁ hr₂
  rw [Real.sqrt_mul (manuscriptResidueEnergy_nonneg hm hB J₁ g₁),
    Real.sqrt_mul (manuscriptResidueEnergy_nonneg hm hB J₂ g₂),
    Real.sqrt_mul (manuscriptAmplitudeEnergy_nonneg hm hB J₁),
    Real.sqrt_mul (manuscriptAmplitudeEnergy_nonneg hm hB J₂),
    Real.sqrt_sq hM₁,Real.sqrt_sq hM₂] at hh
  exact hh.trans_eq (by ring)

end JointDickman

end OAI
