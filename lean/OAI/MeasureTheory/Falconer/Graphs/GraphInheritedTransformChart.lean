import OAI.MeasureTheory.Falconer.Graphs.GraphTransformChart
import OAI.MeasureTheory.Falconer.Angular.GraphRotatedWeights

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem continuous_supported_bump_bound {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |Ψ t| ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (1/4:ℝ) 4)).exists_bound_of_continuousOn
    hΨ.continuousOn
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro t
  by_cases hz : Ψ t = 0
  · simp only [hz, abs_zero]; exact le_max_left _ _
  · exact (hC t (Ioo_subset_Icc_self (hsupp t hz))).trans (le_max_right _ _)

theorem actual_inherited_fourTransform_chart
    {ι : Fin 4 → Type*} (S : ∀ a, Finset (ι a)) (d : ∀ a, ι a → PolicyDescriptor)
    (k : ∀ a, ι a → ℕ) (Q : Fin 4 → DyadicSquare) (hQ : ∀ a, 0 < (Q a).side)
    (ρ : Fin 4 → Measure Plane) [∀ a, IsFiniteMeasure (ρ a)]
    (m : Fin 4 → ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (h : Fin 4 → Plane → ℂ) (hh : ∀ a, Measurable (h a))
    (hhbound : ∀ a x, ‖h a x‖ ≤ 1) (K : Fin 4 → ℕ)
    (hK : ∀ a, ∑ c ∈ S a, k a c ≤ K a)
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (distance plus : Bool) (axis : ℝ) (n j₁ j₂ : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) {R : ℝ} (hR : 0 < R) :
    let b := fun a => inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (m a)
      N lam sig J i (h a)
    let W := graphSourceWeight distance plus axis n j₁ j₂
    let caxis := graphSourceChartAxis distance plus
    let μ := Measure.pi (fun a => (ρ a).restrict (X a))
    Integrable (fun p : (ℝ × Plane) × (Fin 4 → Plane) =>
        graphTransport (graphFourKernel b W p.2) Ψ R caxis p.1) (volume.prod μ) ∧
      R⁻¹ • (∫ r : ℝ, ∫ u, ∫ v, Ψ (r/R) • sourceGraphFourTransform ρ X M b W r u v
        ∂sourceArcLength ∂sourceArcLength) =
        ((M 0*M 1)*(M 2*M 3))⁻¹ •
          (∫ p : ℝ × Plane, ∫ x, graphTransport (graphFourKernel b W x) Ψ R caxis p ∂μ) := by
  classical
  dsimp only
  let b := fun a => inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (m a)
    N lam sig J i (h a)
  let B : Fin 4 → ℝ := fun a => symbolDerivativeConstant (K a)^(K a)
  have hB : ∀ a, 0 ≤ B a := fun a =>
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le (K a))) _
  have hb : ∀ a, Measurable (fun p : Plane × UnitCircle => b a p.1 p.2) := fun a =>
    measurable_inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (m a)
      N lam sig J i (h a) (hh a)
  have hbcont : ∀ a x, Continuous (b a x) := fun a x =>
    inheritedCircleSymbol_continuous (S a) (d a) (k a) (Q a) (hQ a) (ρ a) (m a)
      N lam sig J i (h a) x
  have hbound : ∀ a x ω, ‖b a x ω‖ ≤ B a := fun a x ω =>
    inheritedCircleSymbol_norm_le (S a) (d a) (k a) (Q a) (hQ a) (ρ a) (m a)
      N lam sig J i (h a) (K a) (hK a) x (hhbound a x) ω
  obtain ⟨C,hC,hc⟩ := continuous_supported_bump_bound hΨ hsupp
  have hW := graphSourceWeight_continuous distance plus axis n j₁ j₂
  have hw := graphSourceWeight_norm_le distance plus axis n j₁ j₂
  have hchart := graphSourceWeight_parameter distance plus axis n j₁ j₂
  exact ⟨graphFourKernel_spatial_integrable _ b _ hb hW.measurable B hB hbound hw
      hΨ.measurable hsupp hC hc R _ hchart,
    sourceGraphFourTransform_chart ρ X M b _ hb hbcont hW B hB hbound hw hΨ hsupp hC hc hR _ hchart⟩

end PlanarFalconer

end OAI
