import OAI.NumberTheory.JointDickman.Probability.HistogramAmplitudeBound
import OAI.NumberTheory.JointDickman.Probability.ResidueProductError

namespace OAI

/-! # The product error for the actual two endpoint histograms -/

namespace JointDickman
open Finset MeasureTheory

noncomputable def manuscriptFourier (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ) (h : ZMod q) : ℂ :=
  unitResidueFourier (fun r => ∑ i ∈ J, manuscriptCellSum m B q g F i r) h

noncomputable def manuscriptApproxFourier (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ) (h : ZMod q) : ℂ :=
  unitResidueFourier (fun r => ∑ i ∈ J, manuscriptCellApprox m B q g F i r) h

noncomputable def manuscriptAmplitudeEnergy (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B))) : ℝ :=
  ((q : ℝ)/(q.totient : ℝ))*((J.card : ℝ)*channelMesh (channelFineCount m B))*
    (∑ i ∈ J, ∑ r : (ZMod q)ˣ, (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
      manuscriptChannel m B q (fun _ => 1) (i,r)^2)

theorem manuscriptAmplitudeEnergy_nonneg {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B))) :
    0 ≤ manuscriptAmplitudeEnergy m B q J := by
  have hδ := (channelMesh_pos (channelFineCount_pos hm hB)).le
  unfold manuscriptAmplitudeEnergy
  positivity

theorem manuscriptFourier_square_bounds {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (F : ℝ → ℂ) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hF : ∀ i ∈ J, ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i), ‖F x‖ ≤ M)
    (hI : ∀ i ∈ J, IntervalIntegrable F volume
      (channelLower (channelFineCount m B) i) (channelUpper (channelFineCount m B) i))
    (hLip : ∀ i ∈ J, ∀ u ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i),
      ∀ v ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i), ‖F u-F v‖ ≤ L*|u-v|) :
    (∑ h : ZMod q, ‖manuscriptFourier m B q J g F h‖^2) ≤ manuscriptAmplitudeEnergy m B q J*M^2 ∧
    (∑ h : ZMod q, ‖manuscriptApproxFourier m B q J g F h‖^2) ≤ manuscriptAmplitudeEnergy m B q J*M^2 ∧
    (∑ h : ZMod q, ‖manuscriptFourier m B q J g F h-manuscriptApproxFourier m B q J g F h‖^2) ≤
      manuscriptAmplitudeEnergy m B q J*(L*channelMesh (channelFineCount m B))^2 := by
  obtain ⟨ha,hc⟩ := manuscript_amplitude_fourier_bounds (q := q) hm hB J g hg F hM hF
  have he := manuscript_histogram_fourier_error (q := q) hm hB J g hg F hL hI hLip
  have hb (x : ℝ) :
      ((q : ℝ)/(q.totient : ℝ))*((J.card : ℝ)*channelMesh (channelFineCount m B))*x*
        (∑ i ∈ J, ∑ r : (ZMod q)ˣ,
          (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
            manuscriptChannel m B q (fun _ => 1) (i,r)^2) =
      manuscriptAmplitudeEnergy m B q J*x := by unfold manuscriptAmplitudeEnergy; ring
  exact ⟨ha.trans_eq (hb _),hc.trans_eq (hb _),he.trans_eq (hb _)⟩

theorem manuscript_histogram_product_error {m B q : ℕ} [NeZero q]
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
      manuscriptFourier m B q J₁ g₁ F₁ h*manuscriptFourier m B q J₂ g₂ F₂ h-
      manuscriptApproxFourier m B q J₁ g₁ F₁ h*manuscriptApproxFourier m B q J₂ g₂ F₂ h else 0‖ ≤
      Real.sqrt (manuscriptAmplitudeEnergy m B q J₁)*Real.sqrt (manuscriptAmplitudeEnergy m B q J₂)*
        channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂) := by
  obtain ⟨_,hc₁,he₁⟩ := manuscriptFourier_square_bounds (q := q) hm hB J₁ g₁ hg₁ F₁ hM₁ hL₁ hF₁ hI₁ hLip₁
  obtain ⟨ha₂,_,he₂⟩ := manuscriptFourier_square_bounds (q := q) hm hB J₂ g₂ hg₂ F₂ hM₂ hL₂ hF₂ hI₂ hLip₂
  have hh := restricted_residue_product_error_bound P _ _ _ _ he₁ he₂ hc₁ ha₂
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
