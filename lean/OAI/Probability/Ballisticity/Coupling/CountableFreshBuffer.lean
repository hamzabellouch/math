import Mathlib
import OAI.Probability.Ballisticity.Coupling.FreshBuffer
import OAI.Probability.Ballisticity.Estimates.BufferFirstFailure

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical Function
namespace DirectionalTransience

lemma weighted_countable_partition_lower {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (A B : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hB : ∀ i, MeasurableSet (B i)) (hdis : Pairwise (Disjoint on A))
    (hsub : ∀ i, B i ⊆ A i) (w : Ω → ℝ≥0∞) (c : ℝ≥0∞)
    (hbound : ∀ i, c*(∫⁻ ω in A i, w ω ∂μ) ≤ ∫⁻ ω in B i, w ω ∂μ) :
    c*(∫⁻ ω in ⋃ i, A i, w ω ∂μ) ≤ ∫⁻ ω in ⋃ i, B i, w ω ∂μ := by
  rw [lintegral_iUnion hA hdis,lintegral_iUnion hB
    (fun i j hij => (hdis hij).mono (hsub i) (hsub j)),←ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum hbound

lemma actualFreshBuffer_countable_branches {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ α c : ℝ, 0 < α ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε →
      ∃ g R : ℝ, 0 < g ∧ 0 < R ∧ ∀ {I : Type} [Countable I]
        (a r : I → ℝ) (_ : ∀ i, R ≤ r i) (z₀ : ℝ)
        (π : (i : I) → Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) (a i)))
        (_ : ∀ i, @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a i))) _ (π i))
        (A : I → Set (Environment d))
        (_ : ∀ i, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a i))] (A i))
        (_ : Pairwise (Disjoint on A))
        (_ : ∀ i η, η ∈ A i → IsProbabilityMeasure (π i η).val ∧
          ∀ᵐ x ∂(π i η).val, z₀+r i ≤ signedCoordinate f (x.2-x.1))
        (w : Environment d → ℝ≥0∞)
        (_ : ∀ i, @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a i))) _
          ((A i).indicator w)),
        let H := fun i => ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (r i)⌋₊
        ENNReal.ofReal c*(∫⁻ ω in ⋃ i, A i, w ω ∂environmentLaw ν) ≤
          ∫⁻ ω in ⋃ i, {ω | ω ∈ A i ∧ BufferStageEvent (realPosition (step e)) f (H i)
            z₀ (r i) ε α g (π i ω).val ω}, w ω ∂environmentLaw ν := by
  obtain ⟨α,c,hα,hc,hchance⟩ := buffer_stage_fresh_success_weights ν hue e f hef htrans
  refine ⟨α,c,hα,hc,fun ε hε => ?_⟩
  obtain ⟨g,R,hg,hR,hgood⟩ := hchance ε hε
  refine ⟨g,R,hg,hR,?_⟩
  intro I _ a r hr z₀ π hπ A hA hdis hvalid w hw
  let ℓ := realPosition (step e)
  let H := fun i => ⌊fluctuationScale (independentConditionedPairLaw ν ℓ)
    (commonIncrementProcess ℓ f 0) (r i)⌋₊
  have hH (i : I) : 0 < H i := (hgood (r i) (hr i)).1
  have hS (i : I) : Disjoint (BelowHeight ℓ (a i)) (BelowHeight ℓ (a i))ᶜ := disjoint_compl_right
  have hC (i : I) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight ℓ (a i)) :
      Strip ℓ x.1 (H i) ⊆ (BelowHeight ℓ (a i))ᶜ ∧ Strip ℓ x.2 (H i) ⊆ (BelowHeight ℓ (a i))ᶜ := by
    constructor
    · intro y hy
      change ¬ dot (realPosition y) ℓ < a i
      have hh := hy.1
      rw [hx.1] at hh
      exact not_lt_of_ge hh
    · intro y hy
      change ¬ dot (realPosition y) ℓ < a i
      have hh := hy.1
      rw [hx.2] at hh
      exact not_lt_of_ge hh
  let B := fun i => {ω | ω ∈ A i ∧ BufferStageEvent ℓ f (H i) z₀ (r i) ε α g (π i ω).val ω}
  have hAm (i : I) : MeasurableSet (A i) := (rowSigma_le _) _ (hA i)
  have hBm (i : I) : MeasurableSet (B i) := by
    apply (hAm i).inter
    have hp := (hπ i).mono (rowSigma_le _) le_rfl
    have hm := (measurableSet_bufferStageEvent_rows ℓ f (hH i) z₀ (r i) ε α g
      (PairAtHeight ℓ (a i)) Set.univ (fun x hx => ⟨Set.subset_univ _,Set.subset_univ _⟩)).preimage
        (hp.prodMk (measurable_id.mono le_rfl (rowSigma_le Set.univ)))
    exact hm
  apply weighted_countable_partition_lower (environmentLaw ν) A B hAm hBm hdis
    (fun i _ h => h.1) w (ENNReal.ofReal c)
  intro i
  have hh := (hgood (r i) (hr i)).2 z₀ (PairAtHeight ℓ (a i)) (BelowHeight ℓ (a i))
    (BelowHeight ℓ (a i))ᶜ (hS i) (hC i) (π i) (hπ i) (A i) (hA i) (hvalid i)
    ((A i).indicator w) (hw i)
  rw [lintegral_congr_ae (ae_restrict_mem (hAm i) |>.mono (fun ω hω => Set.indicator_of_mem hω _))] at hh
  have he : (∫⁻ ω in B i, (A i).indicator w ω ∂environmentLaw ν) =
      ∫⁻ ω in B i, w ω ∂environmentLaw ν := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (hBm i)] with ω hω
    exact Set.indicator_of_mem hω.1 _
  exact he ▸ hh
end DirectionalTransience

end

end

end OAI
