import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeIdealMeasuredTiling
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialAutomorphismTopology
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeIdealStrictWidth

namespace OAI

/-! # The actual inside-letter automorphism in strict-width tilings -/

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

def coneIdealLetterAutomorphism (i : Fin M.letterCount) (t : ℝ) : G ≃ₜ* G :=
  integrateNilpotentLieEquivContinuous e Exp hbij chart hchart dynkin hExp
    (M.coneIdealWordBound_zero C) (M.coneIdealInnerAutomorphism C (t • M.letter i))

theorem coneIdealLetterAutomorphism_apply_exp (i : Fin M.letterCount) (t : ℝ)
    (v : M.coneWordIdeal C) :
    M.coneIdealLetterAutomorphism C e Exp hExp hbij chart hchart dynkin i t (Exp (e v)) =
      Exp (e (M.coneIdealLetterFlow C i t v)) := by
  change exponentialConjugate e Exp hbij (M.coneIdealInnerAutomorphism C (t • M.letter i))
    (Exp (e v)) = _
  rw [exponentialConjugate_apply_exp, M.coneIdealInnerAutomorphism_letter]

/-- The smallness threshold comes from the positive mixed-word widths.
No image inclusion is assumed for the automorphism used in the tiling. -/
theorem exists_coneIdealLetterAutomorphism_threshold
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hpos : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → 0 < s i)
    (β : M.ConeIdealBases C) (hβ : M.IsMaximizingConeIdealBasis C b₀ s β)
    (i : Fin M.letterCount) (hi : s i = 0)
    {a b U : ℝ} (ha : 0 ≤ a) (hab : a < b) (hU : 0 < U) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ t ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) →
      (∀ᶠ r in atTop, |t r| ≤ Real.exp ((U * δ + ε r) * r)) →
      ∀ᶠ r in atTop,
        (M.coneIdealLetterAutomorphism C e Exp hExp hbij chart hchart dynkin i (t r)) ''
          M.coneIdealBox C (Exp ∘ e) (fun l => a * s l) β r 1 ⊆
        M.coneIdealBox C (Exp ∘ e) (fun l => b * s l) β r 1 := by
  obtain ⟨lo, hlo, hw⟩ := M.exists_positive_coneIdeal_width C s hs hpos
  let gap := (b - a) * lo
  let D := ((M.bound : ℝ) + 1) * U
  have hg : 0 < gap := mul_pos (sub_pos.mpr hab) hlo
  have hD : 0 < D := mul_pos (by positivity) hU
  let δ₀ := gap / (2 * D)
  have hδ₀ : 0 < δ₀ := div_pos hg (by positivity)
  have heq : δ₀ * (2 * D) = gap := div_mul_cancel₀ gap (ne_of_gt (by positivity))
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδle t ε hε ht
  have hgap : (M.bound : ℝ) * (U * δ) < (b - a) * lo := by
    have hstep := mul_le_mul_of_nonneg_left hδle hD.le
    calc
      _ ≤ D * δ := by dsimp [D]; nlinarith [mul_pos hU hδ]
      _ ≤ D * δ₀ := hstep
      _ < gap := by nlinarith
  filter_upwards [M.coneIdealLetterFlow_absorbed C b₀ s β hβ i hi ha hab
    (mul_nonneg hU.le hδ.le) hw hgap t ε hε ht] with r hr
  rintro _ ⟨g, ⟨v, rfl, hv⟩, rfl⟩
  refine ⟨M.coneIdealLetterFlow C i (t r) v, ?_, hr v hv⟩
  exact (M.coneIdealLetterAutomorphism_apply_exp C e Exp hExp hbij chart hchart dynkin
    i (t r) v).symm

variable [SimplyConnectedSpace G] [MeasurableSpace G] [BorelSpace G]

omit hbij in
/-- Strict width gives measurable tilings for the actual integrated letter
flow, with the exact exponential cardinality bound. The small-box inclusion
is derived from the nilpotent flow estimate. -/
theorem exists_strict_width_coneIdeal_tiling
    (haar : NilpotentExponentialHaarInput E G)
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hpos : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → 0 < s i)
    (β : M.ConeIdealBases C) (hβ : M.IsMaximizingConeIdealBasis C b₀ s β)
    (i : Fin M.letterCount) (hi : s i = 0)
    {a b U : ℝ} (ha : 0 ≤ a) (hab : a < b) (hU : 0 < U) :
    ∃ (μ : Measure G) (hbij : Function.Bijective Exp) (R δ₀ : ℝ),
      μ.IsHaarMeasure ∧ 0 < R ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ t ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) →
      (∀ᶠ r in atTop, |t r| ≤ Real.exp ((U * δ + ε r) * r)) →
      ∀ᶠ r in atTop,
        ∃ (n : ℕ) (anchor : Fin n → G) (tile : Fin n → Set G),
          (∀ j, anchor j ∈ M.coneIdealBox C (Exp ∘ e) (fun l => b * s l) β r 1) ∧
          (∀ j, MeasurableSet (tile j)) ∧
          Pairwise (fun j k => Disjoint (tile j) (tile k)) ∧
          (⋃ j, tile j) = M.coneIdealBox C (Exp ∘ e) (fun l => b * s l) β r 1 ∧
          (∀ j, tile j ⊆ anchor j •
            ((M.coneIdealLetterAutomorphism C e Exp hExp hbij chart hchart dynkin i (t r)) ''
              M.coneIdealBox C (Exp ∘ e) (fun l => a * s l) β r R)) ∧
          (n : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) *
            Real.exp (r * (columnBasisWeight (fun w : M.coneIdealWordList C =>
              M.coneIdealWordCost C (fun l => b * s l) w) β.val -
                columnBasisWeight (fun w : M.coneIdealWordList C =>
                  M.coneIdealWordCost C (fun l => a * s l) w) β.val)) := by
  obtain ⟨μ, hbij, R, hμ, hR, hinv, htiles⟩ :=
    M.exists_coneIdeal_measured_tiling C e Exp hExp haar dynkin b₀
  obtain ⟨δ₀, hδ₀, hsmall⟩ := M.exists_coneIdealLetterAutomorphism_threshold C e Exp hExp
    hbij chart hchart dynkin b₀ s hs hpos β hβ i hi ha hab hU
  refine ⟨μ, hbij, R, δ₀, hμ, hR, hδ₀, ?_⟩
  intro δ hδ hδle t ε hε ht
  filter_upwards [hsmall δ hδ hδle t ε hε ht, eventually_ge_atTop (0 : ℝ)] with r hr hr0
  exact htiles (fun l => b * s l) (fun l => a * s l) β
    (M.maximizing_coneIdealBasis_smul C b₀ s β hβ (ha.trans hab.le))
    (M.maximizing_coneIdealBasis_smul C b₀ s β hβ ha) r hr0
    (M.coneIdealLetterAutomorphism C e Exp hExp hbij chart hchart dynkin i (t r))
    (hinv (t r • M.letter i)) hr

omit hbij in
/-- The same tiling also bounds every anchor after conjugating back by the
inside-letter flow. Both strict width gaps use one positive threshold. -/
theorem exists_strict_width_tiling_with_anchors
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
      ∀ t ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) →
      (∀ᶠ r in atTop, |t r| ≤ Real.exp ((U * δ + ε r) * r)) →
      ∀ᶠ r in atTop,
        ∃ (n : ℕ) (anchor : Fin n → G) (tile : Fin n → Set G),
          (∀ j, anchor j ∈ M.coneIdealBox C (Exp ∘ e) (fun l => b * s l) β r 1) ∧
          (∀ j, M.coneIdealLetterAutomorphism C e Exp hExp hbij chart hchart dynkin i (-t r)
            (anchor j) ∈ M.coneIdealBox C (Exp ∘ e) (fun l => c * s l) β r 1) ∧
          (∀ j, MeasurableSet (tile j)) ∧
          Pairwise (fun j k => Disjoint (tile j) (tile k)) ∧
          (⋃ j, tile j) = M.coneIdealBox C (Exp ∘ e) (fun l => b * s l) β r 1 ∧
          (∀ j, tile j ⊆ anchor j •
            ((M.coneIdealLetterAutomorphism C e Exp hExp hbij chart hchart dynkin i (t r)) ''
              M.coneIdealBox C (Exp ∘ e) (fun l => a * s l) β r R)) ∧
          (n : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) *
            Real.exp (r * (columnBasisWeight (fun w : M.coneIdealWordList C =>
              M.coneIdealWordCost C (fun l => b * s l) w) β.val -
                columnBasisWeight (fun w : M.coneIdealWordList C =>
                  M.coneIdealWordCost C (fun l => a * s l) w) β.val)) := by
  obtain ⟨μ, hbij, R, δ₁, hμ, hR, hδ₁, htiles⟩ :=
    M.exists_strict_width_coneIdeal_tiling C e Exp hExp chart hchart dynkin
      haar b₀ s hs hpos β hβ i hi ha hab hU
  obtain ⟨δ₂, hδ₂, hlarge⟩ := M.exists_coneIdealLetterAutomorphism_threshold C e Exp hExp
    hbij chart hchart dynkin b₀ s hs hpos β hβ i hi (ha.trans hab.le) hbc hU
  refine ⟨μ, hbij, R, min δ₁ δ₂, hμ, hR, lt_min hδ₁ hδ₂, ?_⟩
  intro δ hδ hδle t ε hε ht
  have hneg : ∀ᶠ r in atTop, |(-t r)| ≤ Real.exp ((U * δ + ε r) * r) := by
    simpa only [abs_neg] using ht
  filter_upwards [htiles δ hδ (hδle.trans (min_le_left _ _)) t ε hε ht,
    hlarge δ hδ (hδle.trans (min_le_right _ _)) (fun r => -t r) ε hε hneg] with r hr hn
  obtain ⟨n, anchor, tile, ha, hm, hd, hu, ht, hc⟩ := hr
  refine ⟨n, anchor, tile, ha, ?_, hm, hd, hu, ht, hc⟩
  intro j
  exact hn ⟨anchor j, ha j, rfl⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
