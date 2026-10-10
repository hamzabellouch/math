import OAI.Combinatorics.Progressions.Dynamics.BudgetedOpenImageComparison

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem open_domain_image_comparison_of_close_derivatives
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (Ω : Set (κ → ℝ)) (hΩ : IsOpen Ω) (ρ χ : (κ → ℝ) → ℝ)
    (hρ : Measurable ρ) (hρi : IntegrableOn ρ Ω) (hρ0 : ∀ x ∈ Ω, 0 ≤ ρ x)
    (hρmass : (∫ x in Ω, ρ x) = 1) (hχ : Measurable χ)
    (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hw : ContDiff ℝ 1 (fun x => Ω.indicator ρ x * χ x))
    (hws : HasCompactSupport (fun x => Ω.indicator ρ x * χ x))
    (hwsΩ : tsupport (fun x => Ω.indicator ρ x * χ x) ⊆ Ω)
    (F : Fin 2 → (κ → ℝ) → (ι → ℝ)) (hF : ∀ t, ContDiffOn ℝ 2 (F t) Ω)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hinv : ∀ x ∈ tsupport (fun x => Ω.indicator ρ x * χ x),
      (selectedDerivative (F 0) J x).IsInvertible)
    (K H : ℝ≥0)
    (hK : ∀ x ∈ tsupport (fun x => Ω.indicator ρ x * χ x),
      ‖(selectedDerivative (F 0) J x).inverse‖ ≤ K)
    (hsmall : ∀ x ∈ tsupport (fun x => Ω.indicator ρ x * χ x),
      (K : ℝ) * (‖fderiv ℝ (F 1) x - fderiv ℝ (F 0) x‖ * ‖J‖) ≤ 1 / 2)
    (hH : ∀ t x, x ∈ tsupport (fun x => Ω.indicator ρ x * χ x) →
      ‖fderiv ℝ (selectedDerivative (F t) J) x‖ ≤ H)
    (B : ℝ≥0) (hB : 0 < (B : ℝ))
    (hbudget : (‖J‖ * (2 * K)) *
        (∑ j, ∫ x, |fderiv ℝ (fun x => Ω.indicator ρ x * χ x) x (Pi.single j 1)|) +
      (Fintype.card κ : ℝ) * (‖J‖ * (2 * K) ^ 2 * H) *
        (∫ x, |Ω.indicator ρ x * χ x|) ≤ B)
    {ε η : ℝ} (hε : 0 < ε) (hcut : (∫ x in Ω, ρ x * (1 - χ x)) ≤ η)
    (hclose : ∀ x, Ω.indicator ρ x * χ x ≠ 0 → dist (F 0 x) (F 1 x) ≤ ε)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x in Ω, ρ x * φ (F 0 x)) - ∫ x in Ω, ρ x * φ (F 1 x)| ≤
      2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt ((B : ℝ) * ε) := by
  have hboth (t : Fin 2) (x : κ → ℝ)
      (hx : x ∈ tsupport (fun x => Ω.indicator ρ x * χ x)) :
      (selectedDerivative (F t) J x).IsInvertible ∧
        ‖(selectedDerivative (F t) J x).inverse‖ ≤ 2 * (K : ℝ) := by
    fin_cases t
    · refine ⟨hinv x hx, (hK x hx).trans ?_⟩
      linarith [K.coe_nonneg]
    · exact selected_inverse_perturbation (F 0) (F 1) J x (hinv x hx) K (hK x hx) (hsmall x hx)
  apply open_domain_image_comparison_of_inverse_bounds Ω hΩ ρ χ hρ hρi hρ0 hρmass hχ hχ01
    hw hws hwsΩ F hF J (fun t x hx => (hboth t x hx).1) (2 * K) H
    (fun t x hx => (hboth t x hx).2) hH B hB ?_ hε hcut hclose φ hφ hbound
  simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using hbudget

end Erdos3

end

end OAI
