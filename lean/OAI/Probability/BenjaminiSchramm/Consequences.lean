import OAI.Probability.BenjaminiSchramm.OperatorGap
import OAI.Probability.BenjaminiSchramm.PublishedConsequences

namespace OAI

open MeasureTheory Filter
open scoped Topology

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem percolationProbability_mono [Countable V] [Countable E]
    (G : BondGraph V E) (x : V) : Monotone (fun p => percolationProbability G p x) := by
  have heq (p : unitInterval) : law p {ω | (cluster G ω x).Infinite} =
      labelLaw {labels : E → unitInterval | (cluster G (openEdges labels p) x).Infinite} := by
    rw [← map_openEdges p, Measure.map_apply (measurable_openEdges p)
      (measurableSet_infinite_cluster G x)]
    rfl
  intro p q hpq
  change ((law p) {ω | (cluster G ω x).Infinite}).toReal ≤
    ((law q) {ω | (cluster G ω x).Infinite}).toReal
  rw [heq p, heq q]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro labels h
  exact h.mono (fun y hy => conn_mono G (openEdges_mono labels hpq) hy)

theorem critical_finite_of_probabilityLaw [Countable V] [Countable E]
    (G : BondGraph V E) (hpc : pc G < 1) (htheta : PercolationProbabilityLaw G) :
    ∀ x, ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite := by
  intro x
  obtain ⟨c, C, δ, _hc, _hC, hδ, hb⟩ := htheta x
  obtain ⟨p, _hp, hmem, hlim⟩ := exists_seq_strictAnti_tendsto' hpc
  have hreal : Tendsto (fun n => (p n : ℝ) - (pc G : ℝ)) atTop (𝓝 0) := by
    simpa using (continuous_subtype_val.tendsto (pc G) |>.comp hlim).sub_const (pc G : ℝ)
  have hnear : ∀ᶠ n in atTop, (p n : ℝ) - (pc G : ℝ) < δ :=
    (tendsto_order.mp hreal).2 δ hδ
  have hzero : percolationProbability G (pc G) x ≤ 0 := by
    have hlim' : Tendsto (fun n => C * ((p n : ℝ) - (pc G : ℝ))) atTop (𝓝 0) := by
      simpa using hreal.const_mul C
    apply ge_of_tendsto hlim'
    filter_upwards [hnear] with n hn
    exact (percolationProbability_mono G x (hmem n).1.le).trans (hb (p n) (hmem n).1 hn).2
  have hmeasure : law (pc G) {ω | (cluster G ω x).Infinite} = 0 := by
    apply (measureReal_eq_zero_iff).mp
    exact le_antisymm hzero measureReal_nonneg
  rw [ae_iff]
  exact hmeasure

def CriticalLawsConclusion (G : BondGraph V E) : Prop :=
  (∀ x, triangleDiagram G (pc G) x ≤ operatorNorm G (pc G) ^ 3 ∧
    triangleDiagram G (pc G) x < ⊤) ∧
  SusceptibilityLaw G ∧ PercolationProbabilityLaw G ∧ CriticalTailLaws G ∧
  (pc G < ptwo G ∧ ptwo G ≤ pexp G) ∧
  ∀ p : unitInterval, p < ptwo G → ExponentialDecay G p

theorem critical_laws_of_mainConclusion [Infinite V]
    (G : BondGraph V E) (hgraph : PublishedSimpleGraph G) (hm : MainConclusion G)
    (hfirst : HutchcroftFirstMomentInput G)
    (htheta : TrianglePercolationProbabilityInput G)
    (hvolume : HutchcroftCriticalVolumeInput G)
    (hradii : HutchcroftCriticalRadiiInput G)
    (hexp : HutchcroftExponentialInput G) :
    CriticalLawsConclusion G := by
  let : Countable V := countable_vertices hgraph.locallyFinite hgraph.connected
  let : Countable E := countable_edges hgraph.locallyFinite
  have hb := (operatorNorm_lt_top_iff G (pc G)).mp hm.2.1
  have hθ := percolationProbabilityLaw_of_publishedInput G hgraph htheta hb
  have hp1 : pc G < 1 := hm.2.2.1.trans_le (ptwo G).2.2
  have hfin := critical_finite_of_probabilityLaw G hp1 hθ
  refine ⟨critical_triangle_of_mainConclusion G hm,
    susceptibilityLaw_of_publishedInput G hgraph hfirst hm.2.2.1, hθ,
    criticalTailLaws_of_publishedInputs G hgraph hvolume hradii hm.2.2.1 hfin,
    exponential_threshold_of_mainConclusion G hgraph hexp hm, ?_⟩
  exact exponentialDecay_of_publishedInput G hgraph hexp

theorem critical_laws_conditional [Infinite V]
    (G : BondGraph V E) (hgraph : PublishedSimpleGraph G) (hh : 0 < hV G)
    (hutchcroft2019 :
      ¬ AutUnimodular (subdivision G) (subdivision_injective G)
        (subdivision_connected G hgraph.connected)
        (subdivision_locallyFinite G hgraph.locallyFinite) →
      pc (subdivision G) < ptwo (subdivision G))
    (hfirst : HutchcroftFirstMomentInput G)
    (htheta : TrianglePercolationProbabilityInput G)
    (hvolume : HutchcroftCriticalVolumeInput G)
    (hradii : HutchcroftCriticalRadiiInput G)
    (hexp : HutchcroftExponentialInput G) :
    CriticalLawsConclusion G := by
  exact critical_laws_of_mainConclusion G hgraph
    (main_conditional G hgraph.connected hgraph.locallyFinite
      hgraph.quasiTransitive hh hutchcroft2019) hfirst htheta hvolume hradii hexp

end Percolation.BenjaminiSchramm

end OAI
