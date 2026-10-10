import OAI.MeasureTheory.Falconer.Angular.LongitudinalCrossTerm
import OAI.MeasureTheory.Falconer.Fourier.ChartSymbolControl

namespace OAI

/-!
# Longitudinal localization on the original descendant cubes

The original spatial labels give the point-to-center error. Both cap
errors are controlled before the radial Fourier decay is used.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem dyadic_longitudinal_cross_term {d : ℕ}
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W) (hz : ∀ t, 4 < t → Ψ t = 0)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (Q₁ Q₂ : DyadicCube d), 0 < Q₁.side → 0 < Q₂.side →
      ∀ (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ (j : ℕ) (row col : List (Fin d → Bool) × List (Fin d → Bool)),
      row.1.length = j → col.1.length = j → row.2.length = j → col.2.length = j →
      ∀ R : ℝ, 1 ≤ R → ∀ v τ δ : ℝ, 0 ≤ δ → 4*Real.pi*R^α ≤ (2 : ℝ)^v*τ →
      (2*Real.sqrt d*(Q₁.side/(2 : ℝ)^j)+8*δ*(Real.sqrt d*Q₁.side))+
        (2*Real.sqrt d*(Q₂.side/(2 : ℝ)^j)+8*δ*(Real.sqrt d*Q₂.side)) ≤ τ/2 →
      ∀ (w₁ w₂ : Sphere d),
      τ < |inner ℝ (w₁ : Space d) ((Q₁.descendant row.1).center-(Q₁.descendant col.1).center)+
        inner ℝ (w₂ : Space d) ((Q₂.descendant row.2).center-(Q₂.descendant col.2).center)| →
      ∀ (η θ : Sphere d → ℝ), Measurable η → Measurable θ →
      (∀ z, |η z| ≤ 1) → (∀ z, |θ z| ≤ 1) →
      (∀ z, η z ≠ 0 → ‖(z : Space d)-(w₁ : Space d)‖ ≤ δ) →
      (∀ z, θ z ≠ 0 → ‖(z : Space d)-(w₂ : Space d)‖ ≤ δ) →
      ∀ (b c : Space d → Sphere d → ℂ),
      Measurable (Function.uncurry b) → Measurable (Function.uncurry c) →
      ∀ B : ℝ, 0 ≤ B → (∀ x z, ‖b x z‖ ≤ B) → (∀ x z, ‖c x z‖ ≤ B) →
      ∀ M₁ M₂ : ℝ,
      ‖endpointCapCrossTerm (μ.restrict (Q₁.descendant row.1).carrier)
        (μ.restrict (Q₁.descendant col.1).carrier) (ν.restrict (Q₂.descendant row.2).carrier)
        (ν.restrict (Q₂.descendant col.2).carrier) M₁ M₁ M₂ M₂ v Ψ b b c c η θ‖ ≤
      |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
        ((B*B)*(B*B)*A*((sphereMeasure d).real univ)^2*
          (((μ.restrict (Q₁.descendant row.1).carrier).prod
            (μ.restrict (Q₁.descendant col.1).carrier)).prod
            ((ν.restrict (Q₂.descendant row.2).carrier).prod
              (ν.restrict (Q₂.descendant col.2).carrier))).real univ*R^(-T)) := by
  obtain ⟨A,hA,hmain⟩ := longitudinal_endpoint_cross_term φ Ψ hφ hΨ hpos hzero hW hΨW hz hα T
  refine ⟨A,hA,?_⟩
  intro Q₁ Q₂ hQ₁ hQ₂ μ ν _ _ j row col hr₁ hc₁ hr₂ hc₂ R hR v τ δ hδ hfreq
    herr w₁ w₂ hbad η θ hη hθ hηbound hθbound hηcap hθcap b c hb hc B hB hbB hcB M₁ M₂
  rw [endpointCapCrossTerm_cellSymbols]
  apply hmain _ _ _ _ R hR v τ δ hδ hfreq w₁ w₂
    ((Q₁.descendant row.1).center-(Q₁.descendant col.1).center)
    ((Q₂.descendant row.2).center-(Q₂.descendant col.2).center) hbad
    η θ hη hθ hηbound hθbound hηcap hθcap
    _ _ _ _ (cellSymbol_measurable _ b hb) (cellSymbol_measurable _ b hb)
    (cellSymbol_measurable _ c hc) (cellSymbol_measurable _ c hc) B hB
    (cellSymbol_bound _ b hB hbB) (cellSymbol_bound _ b hB hbB)
    (cellSymbol_bound _ c hB hcB) (cellSymbol_bound _ c hB hcB)
  intro x hx₁ hx₂
  have he₁ := (cellCapPair_displacement_bounds Q₁ hQ₁ row.1 col.1 hr₁ hc₁ η b b x.1 hδ hx₁).2
  have he₂ := (cellCapPair_displacement_bounds Q₂ hQ₂ row.2 col.2 hr₂ hc₂ θ c c x.2 hδ hx₂).2
  have hδ₁ : 0 ≤ δ*‖(Q₁.descendant row.1).center-(Q₁.descendant col.1).center‖ := by positivity
  have hδ₂ : 0 ≤ δ*‖(Q₂.descendant row.2).center-(Q₂.descendant col.2).center‖ := by positivity
  nlinarith

end Falconer

end OAI
