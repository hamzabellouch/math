import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.Score
import OAI.Probability.CriticalPercolation.Modular.ModularClusterCount
import OAI.Probability.CriticalPercolation.Modular.HeavyClusterNumber
import OAI.Probability.CriticalPercolation.ProductMeasure.ProductConditioning
import OAI.Probability.CriticalPercolation.Clusters.FiniteForcing

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma modularMass_union_ne_top (o : V) (S T : Set V) :
    G.modularMass o (S∪T)≠∞ ↔ G.modularMass o S≠∞ ∧ G.modularMass o T≠∞ := by
  constructor
  · intro h
    exact ⟨ne_top_of_le_ne_top h (G.modularMass_mono o Set.subset_union_left),
      ne_top_of_le_ne_top h (G.modularMass_mono o Set.subset_union_right)⟩
  · rintro ⟨hS,hT⟩
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hS,hT⟩) (G.modularMass_union_le o S T)

lemma finiteMassIndicator_insert (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) (a b : V) (he : G.ends e=s(a,b)) :
    G.finiteMassIndicator (insert e ω) a=G.finiteMassIndicator ω a*G.finiteMassIndicator ω b := by
  have hh : G.modularMass a (G.cluster (insert e ω) a)≠∞ ↔
      G.modularMass a (G.cluster ω a)≠∞ ∧ G.modularMass b (G.cluster ω b)≠∞ := by
    rw [G.cluster_insert_endpoint ω e a b he,G.modularMass_union_ne_top]
    exact and_congr_right (fun _ => not_congr (G.modularMass_eq_top_change_base hc hl a b (G.cluster ω b)))
  by_cases ha : G.modularMass a (G.cluster ω a)=∞ <;>
    by_cases hb : G.modularMass b (G.cluster ω b)=∞
  · have hi : G.modularMass a (G.cluster (insert e ω) a)=∞ := by tauto
    simp [finiteMassIndicator,ha,hb,hi]
  · have hi : G.modularMass a (G.cluster (insert e ω) a)=∞ := by tauto
    simp [finiteMassIndicator,ha,hb,hi]
  · have hi : G.modularMass a (G.cluster (insert e ω) a)=∞ := by tauto
    simp [finiteMassIndicator,ha,hb,hi]
  · have hi := hh.mpr ⟨ha,hb⟩
    simp [finiteMassIndicator,ha,hb,hi]

lemma incidentClusterCount_insert_of_ends (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) (a b : V) (he : G.ends e=s(a,b)) :
    G.incidentClusterCount (insert e ω) e=G.finiteMassIndicator ω a*G.finiteMassIndicator ω b := by
  rw [G.incidentClusterCount_of_ends hc hl _ e a b he,
    ite_eq_left (LazyDFS.prop_openEdge_reachable G (insert e ω) (Set.mem_insert e ω) he),
    G.finiteMassIndicator_insert hc hl ω e a b he]

lemma incidentClusterCount_flip_of_ends (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) (a b : V) (he : G.ends e=s(a,b)) :
    (G.incidentClusterCount ω e).toReal-(G.incidentClusterCount (insert e ω) e).toReal =
    if ¬(G.openGraph ω).Reachable a b ∧
      ¬(G.modularMass a (G.cluster ω a)=∞ ∧ G.modularMass b (G.cluster ω b)=∞) then 1 else 0 := by
  rw [G.incidentClusterCount_of_ends hc hl ω e a b he,G.incidentClusterCount_insert_of_ends hc hl ω e a b he]
  by_cases hr : (G.openGraph ω).Reachable a b
  · have hf := G.finiteMassIndicator_eq_of_reachable hc hl ω hr
    rw [ite_eq_left hr,←hf]
    unfold finiteMassIndicator
    split_ifs <;> simp_all
  · simp only [ite_eq_right hr]
    unfold finiteMassIndicator
    by_cases ha : G.modularMass a (G.cluster ω a)=∞ <;>
      by_cases hb : G.modularMass b (G.cluster ω b)=∞ <;> norm_num [ha,hb,hr]

lemma forceOn_univ_singleton (e : E) (ω : Set E) :
    BernoulliProduct.forceOn {e} Set.univ ω=insert e ω := by
  ext f
  by_cases hf : f=e <;> simp [hf]

lemma forceOn_empty_singleton (e : E) (ω : Set E) :
    BernoulliProduct.forceOn {e} ∅ ω=ω\{e} := BernoulliProduct.forceOn_empty_eq_sdiff {e} ω

end CriticalPercolation.BondGraph
end
end

end OAI
