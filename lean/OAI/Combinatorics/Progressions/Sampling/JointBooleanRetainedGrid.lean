import OAI.Combinatorics.Progressions.Probability.RandomCoefficientMassComparison

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α Z W : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  [MeasurableSpace Z] [MeasurableSpace W]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

theorem exists_joint_boolean_retained_grid_stability
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (hsets : ∀ d, Function.Injective (sets d)) (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (hclow : ∀ d o, c₀ d ≤ |c d (block d o)|) (hcup : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition) :
    ∃ sel : ∀ d, O d → Option α, ∀ η : D → ℝ, (∀ d, 0 < η d) →
      let κ := fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d)
      let r := fun d (_ : B d × Fin (h d)) =>
        scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
      let v := fun d => (⟨0, hh d⟩ : Fin (h d))
      let w := jointBooleanGoodWeight c sets block v sel ψ r κ
      let S := jointBooleanWeightBudget (O := O) (α := α) h C A T r κ
      ∀ K H : ℝ≥0,
      (∀ d, productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
        (h d) (C d) 1 (κ d) ≤ K) →
      (∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
        (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ H) →
      ∀ (μ : Measure Z), IsProbabilityMeasure μ → ∀ grid : Z → W, Measurable grid →
      ∀ V : Z × (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ), Measurable V →
      (∀ z, ContDiff ℝ 2 (fun x => V (z, x))) →
      (∀ z x, x ∈ tsupport w →
        (K : ℝ) * ‖fderiv ℝ (fun y => V (z, y)) x - fderiv ℝ (jointBooleanSampler h c sets) x‖ ≤ 1 / 2) →
      (∀ z x, x ∈ tsupport w →
        ‖fderiv ℝ (selectedDerivative (fun y => V (z, y)) (jointBooleanInjection block v sel)) x‖ ≤ H) →
      ∀ ε : ℝ, 0 < ε → (∀ z x, w x ≠ 0 → dist (jointBooleanSampler h c sets x) (V (z, x)) ≤ ε) →
      ∀ φ : W × ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        let Q := 1 + 2 * (K : ℝ) * S +
          (Fintype.card (JointBlockParameter B h α) : ℝ) * ((2 * (K : ℝ)) ^ 2 * H)
        |(∫ p, φ (grid p.1, jointBooleanSampler h c sets p.2) ∂μ.prod (jointBooleanSource h)) -
          ∫ p, φ (grid p.1, V p) ∂μ.prod (jointBooleanSource h)| ≤
          2 * (∑ d, η d) + 4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * ε) := by
  obtain ⟨sel, hsel⟩ := exists_joint_boolean_stability c sets hsets h hh hcard block hblock
    c₀ C hc₀ hC hclow hcup ψ hψ hrange hzero hone A T hLip hTransition
  refine ⟨sel, ?_⟩
  intro η hη
  dsimp only
  intro K H hK hH μ hμ grid hgrid V hV hVs hsmall hHV ε hε hclose φ hφ hbound
  let : IsProbabilityMeasure μ := hμ
  apply retained_image_comparison_of_fiber_bounds μ (jointBooleanSource h)
    (fun p => jointBooleanSampler h c sets p.2) V
    ((jointBooleanSampler_contDiff h c sets).continuous.measurable.comp measurable_snd)
    hV grid hgrid _ φ hφ hbound
  intro z f hf hb
  exact hsel η hη K H hK hH (fun x => V (z, x)) (hVs z) (hsmall z) (hHV z)
    ε hε (hclose z) f hf hb

end Erdos3

end

end OAI
