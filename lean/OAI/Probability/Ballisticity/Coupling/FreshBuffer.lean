import Mathlib
import OAI.Probability.Ballisticity.Walk.FreshRowWeights

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem buffer_stage_fresh_success_weights {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε →
      ∃ g R : ℝ, 0 < g ∧ 0 < R ∧ ∀ r : ℝ, R ≤ r →
        let H := ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊
        0 < H ∧ ∀ (z₀ : ℝ) (C : Set (Lattice d × Lattice d)) (S T : Set (Lattice d)),
          Disjoint S T →
          (∀ x ∈ C, Strip (realPosition (step e)) x.1 H ⊆ T ∧
            Strip (realPosition (step e)) x.2 H ⊆ T) →
          ∀ π : Environment d → SupportedPairMeasures C,
          @Measurable _ _ (rowSigma S) _ π →
          ∀ A : Set (Environment d), MeasurableSet[rowSigma S] A →
          (∀ η ∈ A, IsProbabilityMeasure (π η).val ∧
            ∀ᵐ x ∂(π η).val, z₀+r ≤ signedCoordinate f (x.2-x.1)) →
          ∀ w : Environment d → ℝ≥0∞, @Measurable _ _ (rowSigma S) _ w →
          ENNReal.ofReal c*(∫⁻ ω in A, w ω ∂environmentLaw ν) ≤
            ∫⁻ ω in {ω | ω ∈ A ∧ BufferStageEvent (realPosition (step e)) f H z₀ r ε a g
              (π ω).val ω}, w ω ∂environmentLaw ν := by
  obtain ⟨a,c,ha,hc,hchance⟩ := buffer_stage_success_probability ν hue e f hef htrans
  refine ⟨a,c,ha,hc,fun ε hε => ?_⟩
  obtain ⟨g,R,hg,hR,hgood⟩ := hchance ε hε
  refine ⟨g,R,hg,hR,fun r hr => ?_⟩
  let H := ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
    (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊
  obtain ⟨hH,hπgood⟩ := hgood r hr
  refine ⟨hH,fun z₀ C S T hST hC π hπ A hA hvalid w hw => ?_⟩
  apply fresh_buffer_weighted_test ν (realPosition (step e)) f hH z₀ r ε a g C hST hC π hπ A hA w hw
  intro η hη
  obtain ⟨hprob,hgap⟩ := hvalid η hη
  let := hprob
  have hb := hπgood z₀ (π η).val hprob hgap
  have he : {ω | BufferStageEvent (realPosition (step e)) f H z₀ r ε a g (π η).val ω} =
      {ω | BufferStageSuccess (realPosition (step e)) f H z₀ r ε a g (π η).val ω} := by
    ext ω
    exact bufferStageEvent_iff e f hH z₀ r ε a hg.le (π η).val ω
  rw [he]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr hb
end DirectionalTransience

end

end

end OAI
