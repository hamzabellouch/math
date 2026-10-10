import OAI.MeasureTheory.Falconer.Angular.LongitudinalCapTerm
import OAI.MeasureTheory.Falconer.Angular.CapAmplitudeDerivatives

namespace OAI

/-!
# The longitudinal error for the original four endpoint transforms

The radial estimate is applied before absolute values or spatial summation.
The endpoint symbols may be merely measurable in the spatial labels.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem longitudinal_endpoint_cross_term {d : ℕ}
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W) (hz : ∀ t, 4 < t → Ψ t = 0)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (μ μ' ν ν' : Measure (Space d))
        [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν'],
      ∀ R : ℝ, 1 ≤ R → ∀ v τ δ : ℝ, 0 ≤ δ → 4*Real.pi*R^α ≤ (2 : ℝ)^v*τ →
      ∀ (w₁ w₂ d₁ d₂ : Space d), τ < |inner ℝ w₁ d₁+inner ℝ w₂ d₂| →
      ∀ (η θ : Sphere d → ℝ), Measurable η → Measurable θ →
      (∀ z, |η z| ≤ 1) → (∀ z, |θ z| ≤ 1) →
      (∀ z, η z ≠ 0 → ‖(z : Space d)-w₁‖ ≤ δ) →
      (∀ z, θ z ≠ 0 → ‖(z : Space d)-w₂‖ ≤ δ) →
      ∀ (b b' c c' : Space d → Sphere d → ℂ),
      Measurable (Function.uncurry b) → Measurable (Function.uncurry b') →
      Measurable (Function.uncurry c) → Measurable (Function.uncurry c') →
      ∀ B : ℝ, 0 ≤ B →
      (∀ x z, ‖b x z‖ ≤ B) → (∀ x z, ‖b' x z‖ ≤ B) →
      (∀ x z, ‖c x z‖ ≤ B) → (∀ x z, ‖c' x z‖ ≤ B) →
      (∀ x : (Space d × Space d) × (Space d × Space d),
        (∃ z, capPairAmplitude η b b' x.1 z ≠ 0) →
        (∃ z, capPairAmplitude θ c c' x.2 z ≠ 0) →
        (‖(x.1.1-x.1.2)-d₁‖+δ*‖d₁‖)+(‖(x.2.1-x.2.2)-d₂‖+δ*‖d₂‖) ≤ τ/2) →
      ∀ M M' P P' : ℝ,
      ‖endpointCapCrossTerm μ μ' ν ν' M M' P P' v Ψ b b' c c' η θ‖ ≤
        |(M⁻¹*M'⁻¹)*(P⁻¹*P'⁻¹)| *
          ((B*B)*(B*B)*A*((sphereMeasure d).real univ)^2*
            ((μ.prod μ').prod (ν.prod ν')).real univ*R^(-T)) := by
  let X := (Space d × Space d) × (Space d × Space d)
  obtain ⟨A,hA,hmain⟩ := longitudinal_discarded_cap_term_bound (X := X)
    φ Ψ hφ hΨ hpos hzero hW hΨW hz hα T
  refine ⟨A,hA,?_⟩
  intro μ μ' ν ν' _ _ _ _ R hR v τ δ hδ hfreq w₁ w₂ d₁ d₂ hbad
    η θ hη hθ hηnorm hθnorm hcap₁ hcap₂ b b' c c' hb hb' hc hc'
    B hB hbB hb'B hcB hc'B herr M M' P P'
  let μ₄ := (μ.prod μ').prod (ν.prod ν')
  let a₁ : X → Sphere d → ℂ := fun x z => capPairAmplitude η b b' x.1 z
  let a₂ : X → Sphere d → ℂ := fun x z => capPairAmplitude θ c c' x.2 z
  have ha₁ : Measurable (Function.uncurry a₁) :=
    (capPairAmplitude_measurable η hη b b' hb hb').comp
      (measurable_fst.fst.prodMk measurable_snd)
  have ha₂ : Measurable (Function.uncurry a₂) :=
    (capPairAmplitude_measurable θ hθ c c' hc hc').comp
      (measurable_fst.snd.prodMk measurable_snd)
  have hb₁ (x : X) (z : Sphere d) : ‖a₁ x z‖ ≤ B*B := by
    simpa only [one_mul] using capPairAmplitude_norm_le η b b' zero_le_one hB hηnorm hbB hb'B x.1 z
  have hb₂ (x : X) (z : Sphere d) : ‖a₂ x z‖ ≤ B*B := by
    simpa only [one_mul] using capPairAmplitude_norm_le θ c c' zero_le_one hB hθnorm hcB hc'B x.2 z
  have hh := hmain μ₄ R hR v τ δ hδ hfreq w₁ w₂ d₁ d₂ hbad
    (fun x => x.1.1-x.1.2) (fun x => x.2.1-x.2.2) (by fun_prop) (by fun_prop)
    a₁ a₂ ha₁ ha₂
    (fun x z hz => capPairAmplitude_cap_support η b b' w₁ δ hcap₁ x.1 z hz)
    (fun x z hz => capPairAmplitude_cap_support θ c c' w₂ δ hcap₂ x.2 z hz)
    herr (B*B) (B*B) (mul_nonneg hB hB) (mul_nonneg hB hB) hb₁ hb₂
  rw [endpointCapCrossTerm_four_point,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hh (abs_nonneg _)

end Falconer

end OAI
