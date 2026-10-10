import Mathlib
import OAI.Probability.Ballisticity.Estimates.GridOscillation

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma compact_path_modulus (K : Set C(unitInterval,ℝ)) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ Disjoint K (ContinuousOscillation ε δ) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun p : K × unitInterval => p.1.1 p.2) :=
    continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨δ,hδ,hm⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hc) ε hε
  refine ⟨δ/2,by positivity,Set.disjoint_left.mpr ?_⟩
  rintro f hf ⟨s,t,hst,hbig⟩
  have hd : dist ((⟨f,hf⟩ : K),s) ((⟨f,hf⟩ : K),t) < δ := by
    simpa only [Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using hst.trans_lt (half_lt_self hδ)
  have hh := hm hd
  exact (not_lt_of_ge hbig.le) (by simpa only [Real.dist_eq] using hh)

lemma tight_path_modulus (μ : ℕ → Measure C(unitInterval,ℝ))
    (ht : IsTightMeasureSet (Set.range μ)) {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) :
    ∃ δ, 0 < δ ∧ ∀ i, μ i (ContinuousOscillation ε δ) ≤ ENNReal.ofReal β := by
  obtain ⟨K,hK,hKm⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht (ENNReal.ofReal β) (ENNReal.ofReal_pos.mpr hβ)
  obtain ⟨δ,hδ,hd⟩ := compact_path_modulus K hK hε
  have hsub : ContinuousOscillation ε δ ⊆ Kᶜ := by
    intro f hf hfK
    exact Set.disjoint_left.mp hd hfK hf
  exact ⟨δ,hδ,fun i => (measure_mono hsub).trans (hKm _ (Set.mem_range_self i))⟩

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
