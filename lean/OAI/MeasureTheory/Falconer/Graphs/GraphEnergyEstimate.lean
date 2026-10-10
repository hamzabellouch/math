import OAI.MeasureTheory.Falconer.Estimates.DyadicEnergyStep
import OAI.MeasureTheory.Falconer.Estimates.DyadicLocalization

namespace OAI

/-!
# The graph energy estimate before profile normalization

This assembles the exact splitting, proved localization and retained
Schur bound. All endpoint symbols, including reached anchor masks, remain
unchanged on children. The numerical error is explicit.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

noncomputable def capGraphError (d m : ℕ) (A C W R T M₁ M₂ H B D v τ : ℝ) (K S : ℕ) : ℝ :=
  (K : ℝ)^2*(S : ℝ)^2 *
    (|(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
      (A*(4^m*H*B*B)*(B*B)*(sphereMeasure d).real univ) *
        (16*D/((2 : ℝ)^v*τ))^m*(4*W) +
    |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
      ((B*B)*(B*B)*C*((sphereMeasure d).real univ)^2*R^(-T)))

theorem dyadic_graph_energy_step
    (hpublished : PublishedGnomonicSurface) (n m : ℕ) (hn : 1 ≤ n)
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ (Q₁ Q₂ : DyadicCube (n+2)), 0 < Q₁.side → Q₂.side = Q₁.side →
      ∀ (μ ν : Measure (Space (n+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (j : ℕ) (R : ℝ), 1 ≤ R → ∀ (v τ δ H B D : ℝ), 0 < τ → 0 < δ → δ ≤ 1/2 →
      0 ≤ H → 0 ≤ B → 1 ≤ D → δ⁻¹ ≤ D →
      Real.sqrt (n+2 : ℕ)*Q₁.side ≤ (τ/4)*D →
      2*Real.sqrt (n+2 : ℕ)*(Q₁.side/(2 : ℝ)^j)+8*δ*(Real.sqrt (n+2 : ℕ)*Q₁.side) ≤ τ/4 →
      4*Real.pi*R^α ≤ (2 : ℝ)^v*τ →
      ∀ (Ma₁ Ma₂ Mp₁ Mp₂ a p : ℝ), 0 < Ma₁ → 0 < Ma₂ → 0 < Mp₁ → 0 < Mp₂ →
      ∀ {κ : Type*} (K : Finset κ) (w : κ → Sphere (n+2)) (η : κ → Sphere (n+2) → ℝ),
      (∀ k ∈ K, ChartCapControl m (η k) (w k : Space (n+2)) δ H) →
      (∀ k ∈ K, ∀ z, 0 ≤ η k z) → (∀ z, ∑ k ∈ K, η k z = 1) →
      ∀ (b c : Space (n+2) → Sphere (n+2) → ℂ),
      ChartSymbolControl m b B D → ChartSymbolControl m c B D →
      ∀ (g₁ g₂ L C₁ C₂ : ℕ), g₁ ≤ j → g₂ ≤ j →
      4*τ*((2 : ℝ)^j/Q₁.side) ≤ L →
      ∀ W₁ W₂ : ℝ,
      2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*(Q₁.side/(2 : ℝ)^g₁)) ≤ W₁ →
      2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*(Q₂.side/(2 : ℝ)^g₂)) ≤ W₂ →
      (∀ q ∈ Q₁.occupiedPaths μ j, ∀ᵐ x ∂μ.restrict (Q₁.descendant q).carrier,
        ∀ z : Sphere (n+2), b x z ≠ 0 →
          DyadicParallelTest Q₁ (Q₁.occupiedPaths μ j) g₁ q (z : Space (n+2)) W₁ C₁) →
      (∀ q ∈ Q₂.occupiedPaths ν j, ∀ᵐ x ∂ν.restrict (Q₂.descendant q).carrier,
        ∀ z : Sphere (n+2), c x z ≠ 0 →
          DyadicParallelTest Q₂ (Q₂.occupiedPaths ν j) g₂ q (z : Space (n+2)) W₂ C₂) →
      ∀ [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)],
      independentAngularEnergy a v Ψ
        (fun z => endpointTransform (μ.restrict Q₁.carrier) Ma₁ b z.1 z.2)
        (fun z => endpointTransform (ν.restrict Q₂.carrier) Ma₂ c z.1 z.2) ≤
      ((Mp₁/Ma₁)*(Mp₂/Ma₂))^2 *
        ((2 : ℝ)^(((n+2 : ℕ) : ℝ)*(p-a)) *
          ((2*L+1)^(n+2) * min (C₁*2^((n+2)*g₁)) (C₂*2^((n+2)*g₂)) : ℕ) *
          ∑ row ∈ Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j,
            independentAngularEnergy p v Ψ
              (fun z => endpointTransform (μ.restrict (Q₁.descendant row.1).carrier) Mp₁ b z.1 z.2)
              (fun z => endpointTransform (ν.restrict (Q₂.descendant row.2).carrier) Mp₂ c z.1 z.2)) +
        (2 : ℝ)^(((n+2 : ℕ) : ℝ)*(v-a))*((Mp₁/Ma₁)*(Mp₂/Ma₂))^2 *
          capGraphError (n+2) m A C W R T Mp₁ Mp₂ H B D v τ K.card
            (Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j).card := by
  obtain ⟨A,C,hA,hC,hloc⟩ := dyadic_localization_error hpublished n m hn φ Ψ
    hφ hΨ hpos hzero hW hΨW hsupp hα T
  refine ⟨A,C,hA,hC,?_⟩
  intro Q₁ Q₂ hQ hside μ ν _ _ j R hR v τ δ H B D hτ hδ hδsmall
    hH hB hD hδD hnorm herr hfreq Ma₁ Ma₂ Mp₁ Mp₂ a p hMa₁ hMa₂ hMp₁ hMp₂
    κ K w η hcap hη hpart b c hb hc g₁ g₂ L C₁ C₂ hg₁ hg₂ hL W₁ W₂ hw₁ hw₂ hs₁ hs₂ _
  apply independentAngularEnergy_of_localization Q₁ Q₂ hQ hside μ ν Ma₁ Ma₂ Mp₁ Mp₂
    hMa₁ hMa₂ hMp₁ hMp₂ b c hb.measurable hc.measurable hB hb.bound hc.bound K η w
    hη hpart hδ.le (fun k hk z hz => (hcap k hk).support z (ne_of_gt hz))
    hg₁ hg₂ hL hw₁ hw₂ hs₁ hs₂ a p v Ψ
  exact hloc Q₁ Q₂ hQ hside μ ν j R hR v τ δ H B D hτ hδ hδsmall
    hH hB hD hδD hnorm herr hfreq Mp₁ Mp₂ hMp₁ hMp₂ K w η hcap hη b c hb hc

end Falconer

end OAI
