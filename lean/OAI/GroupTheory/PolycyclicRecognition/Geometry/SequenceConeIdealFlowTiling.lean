import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConeIdealFlowTiling
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceRealExtension

namespace OAI

/-! # Strict-width tilings on the actual profile scales -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule MeasureTheory Set Filter
open scoped Manifold Topology Pointwise

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  (e : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
  (dynkin : NilpotentDynkinExpansionInput E G)

variable [SimplyConnectedSpace G] [MeasurableSpace G] [BorelSpace G]

omit hbij in
/-- Actual flow tilings along any strictly increasing profile scale sequence,
with the same threshold, cardinality and reverse-anchor estimates. -/
theorem exists_strict_width_sequence_tiling_with_anchors
    (haar : NilpotentExponentialHaarInput E G)
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hpos : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → 0 < s i)
    (β : M.ConeIdealBases C) (hβ : M.IsMaximizingConeIdealBasis C b₀ s β)
    (i : Fin M.letterCount) (hi : s i = 0)
    {a b c U : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hU : 0 < U) :
    ∃ (μ : Measure G) (hbij : Function.Bijective Exp) (R δ₀ : ℝ),
      μ.IsHaarMeasure ∧ 0 < R ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (scale : ℕ → ℝ), StrictMono scale → Tendsto scale atTop atTop →
      ∀ t ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) →
      (∀ᶠ m in atTop, |t m| ≤ Real.exp ((U * δ + ε m) * (scale m))) →
      ∀ᶠ m in atTop,
        ∃ (n : ℕ) (anchor : Fin n → G) (tile : Fin n → Set G),
          (∀ j, anchor j ∈ M.coneIdealBox C (Exp ∘ e) (fun l => b * s l) β (scale m) 1) ∧
          (∀ j, M.coneIdealLetterAutomorphism C e Exp hExp hbij chart hchart dynkin i (-t m)
            (anchor j) ∈ M.coneIdealBox C (Exp ∘ e) (fun l => c * s l) β (scale m) 1) ∧
          (∀ j, MeasurableSet (tile j)) ∧
          Pairwise (fun j k => Disjoint (tile j) (tile k)) ∧
          (⋃ j, tile j) = M.coneIdealBox C (Exp ∘ e) (fun l => b * s l) β (scale m) 1 ∧
          (∀ j, tile j ⊆ anchor j •
            ((M.coneIdealLetterAutomorphism C e Exp hExp hbij chart hchart dynkin i (t m)) ''
              M.coneIdealBox C (Exp ∘ e) (fun l => a * s l) β (scale m) R)) ∧
          (n : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) *
            Real.exp ((scale m) * (columnBasisWeight (fun w : M.coneIdealWordList C =>
              M.coneIdealWordCost C (fun l => b * s l) w) β.val -
                columnBasisWeight (fun w : M.coneIdealWordList C =>
                  M.coneIdealWordCost C (fun l => a * s l) w) β.val)) := by
  obtain ⟨μ, hbij, R, δ₀, hμ, hR, hδ₀, htiles⟩ :=
    M.exists_strict_width_tiling_with_anchors C e Exp hExp chart hchart dynkin
      haar b₀ s hs hpos β hβ i hi ha hab hbc hU
  refine ⟨μ, hbij, R, δ₀, hμ, hR, hδ₀, ?_⟩
  intro δ hδ hδle scale hmono hscale t ε hε ht
  have hεreal := tendsto_sequenceRealExtension_zero scale hmono ε hε
  have htreal := sequenceRealExtension_eventually_abs_le_exp scale hmono t ε (U * δ) ht
  have hh := hscale.eventually (htiles δ hδ hδle
    (sequenceRealExtension scale t) (sequenceRealExtension scale ε) hεreal htreal)
  simpa only [sequenceRealExtension_apply scale hmono] using hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
