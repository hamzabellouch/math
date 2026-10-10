import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.Score
import OAI.Probability.CriticalPercolation.Modular.CriticalHeavyDrop
import OAI.Probability.CriticalPercolation.Modular.HeavyFiniteGeometry

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma critical_root_adjacent_heavy_null [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hp0 : 0<G.criticalProbability) (hp1 : G.criticalProbability<1) (o x y : V)
    (hx : x∈(G.orbitRepresentatives hq).roots) (hxy : G.fullGraph.Adj x y) :
    G.law G.criticalProbability (G.distinctHeavyEvent o x y)=0 := by
  obtain ⟨⟨e,_,he⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
  have hae := G.critical_root_incident_drop_ae hc hl hq hp0 hp1 x hx e (by simp [he])
  have han : ∀ᵐ ω ∂G.law G.criticalProbability, ω∉G.distinctHeavyEvent o x y := by
    filter_upwards [hae] with ω hω hbad
    obtain ⟨hxH,hyH,hR⟩ := hbad
    have hclosed : e∉ω := fun h => hR (LazyDFS.prop_openEdge_reachable G ω h he)
    have hs : ω\{e}=ω := by ext f; by_cases hf : f=e <;> simp_all
    have hx' : G.modularMass x (G.cluster ω x)=∞ :=
      (G.modularMass_eq_top_change_base hc hl o x _).mp hxH
    have hy' : G.modularMass y (G.cluster ω y)=∞ :=
      (G.modularMass_eq_top_change_base hc hl o y _).mp hyH
    rw [G.disconnectedIndicator_of_ends ω e x y he,G.clusterCountDrop_of_ends hc hl ω e x y he,hs] at hω
    norm_num [hR,hx',hy'] at hω
  rw [ae_iff] at han
  simpa only [not_not,Set.ofPred_mem_eq] using han

lemma critical_adjacent_heavy_null [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hp0 : 0<G.criticalProbability) (hp1 : G.criticalProbability<1) (o x y : V)
    (hxy : G.fullGraph.Adj x y) :
    G.law G.criticalProbability (G.distinctHeavyEvent o x y)=0 := by
  obtain ⟨r,hr,φ,hφ⟩ := (G.orbitRepresentatives hq).cover x
  obtain ⟨s,hs⟩ := φ.vertex.surjective y
  rw [←hφ,←hs,φ.distinctHeavyEvent_measure G hc hl]
  exact G.critical_root_adjacent_heavy_null hc hl hq hp0 hp1 o r s hr
    ((φ.fullGraph_adj G r s).mp (by simpa only [hφ,hs] using hxy))

theorem atMostOneHeavy_critical_ae (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hp1 : G.criticalProbability<1) (o : V) :
    ∀ᵐ ω ∂G.law G.criticalProbability, ω∈G.atMostOneHeavy o := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  by_cases hp0 : 0<G.criticalProbability
  · exact G.atMostOneHeavy_ae_of_adjacent_null hc G.criticalProbability hp0 o
      (fun x y hxy => G.critical_adjacent_heavy_null hc hl hq hp0 hp1 o x y hxy)
  · have he : G.criticalProbability=0 := le_antisymm (le_of_not_gt hp0) (unitInterval.nonneg _)
    rw [he]
    have hnull := G.law_zero_percolates
    have hnp : ∀ᵐ ω ∂G.law 0, ω∉G.percolates := by
      rw [ae_iff]
      simpa only [not_not,Set.ofPred_mem_eq] using hnull
    filter_upwards [hnp] with ω hω
    intro x y hx hy
    exact False.elim (hω ⟨x,G.infinite_of_modularMass_top o hx⟩)

end CriticalPercolation.BondGraph
end
end

end OAI
