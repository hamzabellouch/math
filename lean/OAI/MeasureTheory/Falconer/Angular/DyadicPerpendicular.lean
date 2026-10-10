import OAI.MeasureTheory.Falconer.Fourier.ChartSymbolControl
import OAI.MeasureTheory.Falconer.Angular.PerpendicularCrossTerm
import OAI.MeasureTheory.Falconer.Angular.DyadicCapTerms

namespace OAI

/-!
# Perpendicular localization on actual descendant cubes

The small point-to-center error and derivative hypotheses are verified
for the original cell-restricted symbols before applying the cap estimate.
-/

namespace Falconer
open Set MeasureTheory

theorem dyadic_perpendicular_cross_term
    (hpublished : PublishedGnomonicSurface) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (Q₁ Q₂ : DyadicCube (n+2)), 0 < Q₁.side →
      ∀ (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ (j : ℕ) (row col : List (Fin (n+2) → Bool) × List (Fin (n+2) → Bool)),
      row.1.length = j → col.1.length = j →
      ∀ (w : Sphere (n+2)) (τ δ H B D : ℝ), 0 < τ → 0 < δ → δ ≤ 1/2 →
      0 ≤ H → 0 ≤ B → 1 ≤ D → δ⁻¹ ≤ D →
      Real.sqrt (n+2 : ℕ)*Q₁.side ≤ (τ/4)*D →
      2*Real.sqrt (n+2 : ℕ)*(Q₁.side/(2 : ℝ)^j)+8*δ*(Real.sqrt (n+2 : ℕ)*Q₁.side) ≤ τ/2 →
      τ < ‖perpendicularPart (w : Space (n+2))
        ((Q₁.descendant row.1).center-(Q₁.descendant col.1).center)‖ →
      ∀ (η θ : Sphere (n+2) → ℝ), ChartCapControl m η (w : Space (n+2)) δ H →
      Measurable θ → (∀ z, |θ z| ≤ 1) →
      ∀ (b c : Space (n+2) → Sphere (n+2) → ℂ),
      ChartSymbolControl m b B D → Measurable (Function.uncurry c) → (∀ x z, ‖c x z‖ ≤ B) →
      ∀ (M₁ M₂ v : ℝ) (Ψ : ℝ → ℝ), 0 < M₁ → 0 < M₂ →
      Measurable Ψ → (∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4) →
      ∀ W : ℝ, 0 ≤ W → (∀ t, Ψ t ≤ W) →
      ‖endpointCapCrossTerm (μ.restrict (Q₁.descendant row.1).carrier)
        (μ.restrict (Q₁.descendant col.1).carrier) (ν.restrict (Q₂.descendant row.2).carrier)
        (ν.restrict (Q₂.descendant col.2).carrier) M₁ M₁ M₂ M₂ v Ψ b b c c η θ‖ ≤
      |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
        (A*(4^m*H*B*B)*(B*B)*(sphereMeasure (n+2)).real univ*
          (((μ.restrict (Q₁.descendant row.1).carrier).prod
            (μ.restrict (Q₁.descendant col.1).carrier)).prod
            ((ν.restrict (Q₂.descendant row.2).carrier).prod
              (ν.restrict (Q₂.descendant col.2).carrier))).real univ) *
        (16*D/((2 : ℝ)^v*τ))^m*(4*W) := by
  obtain ⟨A,hA,hmain⟩ := perpendicular_endpoint_cross_term hpublished n m hn
  refine ⟨A,hA,?_⟩
  intro Q₁ Q₂ hQ μ ν _ _ j row col hrow hcol w τ δ H B D hτ hδ hδsmall
    hH hB hD hδD hnorm herr hbad η θ hη hθ hθbound b c hb hc hcB
    M₁ M₂ v Ψ _hM₁ _hM₂ hΨ hΨsupp W hW hΨW
  have hbrow := hb.cell hB (zero_le_one.trans hD) (Q₁.descendant row.1)
  have hbcol := hb.cell hB (zero_le_one.trans hD) (Q₁.descendant col.1)
  have hcRow := cellSymbol_measurable (Q₂.descendant row.2) c hc
  have hcCol := cellSymbol_measurable (Q₂.descendant col.2) c hc
  rw [endpointCapCrossTerm_cellSymbols]
  apply hmain w ((Q₁.descendant row.1).center-(Q₁.descendant col.1).center)
    τ δ (sphere_norm w) hτ hδ hδsmall hbad
    _ _ _ _ η θ hη.measurable hθ hη.bound hθbound hη.support
    _ _ _ _ hbrow.measurable hbcol.measurable hcRow hcCol
    hη.smooth hbrow.smooth hbcol.smooth H B D hH hB hD hδD
    hbrow.bound hbcol.bound
    (cellSymbol_bound _ c hB hcB) (cellSymbol_bound _ c hB hcB)
    hη.derivative hbrow.derivative hbcol.derivative
  · intro x hx
    exact ((cellCapPair_displacement_bounds Q₁ hQ row.1 col.1 hrow hcol η b b
      x hδ.le hx).1).trans hnorm
  · intro x hx
    exact ((cellCapPair_displacement_bounds Q₁ hQ row.1 col.1 hrow hcol η b b
      x hδ.le hx).2).trans herr
  · exact hΨ
  · exact hΨsupp
  · exact hW
  · exact hΨW

end Falconer

end OAI
