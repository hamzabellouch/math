import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Criticality.FiniteEnergy
import OAI.Probability.CriticalPercolation.Clusters.CriticalClusterMultiplicity

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def separatedInfiniteTupleEvent {k : ℕ} (v : Fin k → V) : Set (Set E) :=
  {ω | (∀ i, (G.cluster ω (v i)).Infinite) ∧
    Pairwise (fun i j => ¬(G.openGraph ω).Reachable (v i) (v j))}

def encounterEvent (J : Set E) (o : V) (k : ℕ) : Set (Set E) :=
  {ω | ∃ v : Fin k → V, (∀ i, (G.openGraph ω).Reachable o (v i)) ∧
    (∀ i, (G.cluster (ω\J) (v i)).Infinite) ∧
    Pairwise (fun i j => ¬(G.openGraph (ω\J)).Reachable (v i) (v j))}

lemma measurableSet_separatedInfiniteTupleEvent [Countable V] [Countable E]
    {k : ℕ} (v : Fin k → V) : MeasurableSet (G.separatedInfiniteTupleEvent v) := by
  exact ((Measurable.forall fun i => G.measurable_infinite_cluster (v i)).and
    (Measurable.forall fun i => Measurable.forall fun j =>
      measurable_const.imp (G.measurable_reachable (v i) (v j)).not)).setOf

lemma measurableSet_encounterEvent [Countable V] [Countable E]
    (J : Set E) (o : V) (k : ℕ) : MeasurableSet (G.encounterEvent J o k) := by
  have hm : Measurable (fun ω : Set E => ω\J) := by
    exact Measurable.of_eval (fun edge => (measurable_set_mem edge).and measurable_const)
  exact (Measurable.exists fun v : Fin k → V =>
    (Measurable.forall fun i => G.measurable_reachable o (v i)).and
    ((Measurable.forall fun i => (G.measurable_infinite_cluster (v i)).comp hm).and
      (Measurable.forall fun i => Measurable.forall fun j =>
        measurable_const.imp ((G.measurable_reachable (v i) (v j)).comp hm).not))).setOf

lemma infinite_cluster_sdiff_has_infinite (ω J : Set E) (hJ : J.Finite) (v : V)
    (hv : (G.cluster ω v).Infinite) :
    ∃ w, (G.openGraph ω).Reachable v w ∧ (G.cluster (ω\J) w).Infinite := by
  have hsub : ω⊆(ω\J)∪(ω∩J) := by
    intro e he
    by_cases h : e∈J
    · exact Or.inr ⟨he,h⟩
    · exact Or.inl ⟨he,h⟩
  obtain ⟨w,hw,hi⟩ := G.infinite_cluster_union_has_old (ω\J) (ω∩J)
    (hJ.inter_of_right _) v (hv.mono (G.cluster_mono hsub v))
  exact ⟨w,G.cluster_mono (by intro e h; rcases h with h|h; exact h.1; exact h.1) v hw,hi⟩

lemma separatedTuple_force_encounter {k : ℕ} (v : Fin k → V)
    (J : Set E) (hJ : J.Finite) (o : V)
    (hconn : ∀ i, (G.openGraph J).Reachable o (v i))
    (ω : Set E) (hω : ω∈G.separatedInfiniteTupleEvent v) :
    J∪ω∈G.encounterEvent J o k := by
  have h (i : Fin k) := G.infinite_cluster_sdiff_has_infinite ω J hJ (v i) (hω.1 i)
  choose w hw hi using h
  refine ⟨w,?_,?_,?_⟩
  · intro i
    exact (G.cluster_mono Set.subset_union_left o (hconn i)).trans
      (G.cluster_mono Set.subset_union_right (v i) (hw i))
  · simpa only [Set.union_sdiff_left] using hi
  · intro i j hij hpath
    have hpath' : (G.openGraph ω).Reachable (w i) (w j) := by
      apply G.cluster_mono (show (J∪ω)\J⊆ω from fun _ h => by
        rcases h.1 with hh|hh
        · exact False.elim (h.2 hh)
        · exact hh) (w i) hpath
    exact hω.2 hij ((hw i).trans (hpath'.trans (hw j).symm))

lemma exists_positive_separatedTuple [Countable V] [Countable E]
    (p : unitInterval) (k : ℕ)
    (hm : ∀ᵐ ω ∂G.law p, G.infinitelyManyInfiniteClusters ω) :
    ∃ v : Fin k → V, 0<G.law p (G.separatedInfiniteTupleEvent v) := by
  by_contra h
  have hall : ∀ v : Fin k → V, G.law p (G.separatedInfiniteTupleEvent v)=0 := by
    intro v
    exact le_antisymm (le_of_not_gt (fun hv => h ⟨v,hv⟩)) bot_le
  have hn : G.law p (⋃ v : Fin k → V, G.separatedInfiniteTupleEvent v)=0 :=
    measure_iUnion_null hall
  have he : ∀ᵐ ω ∂G.law p, ω∈⋃ v : Fin k → V, G.separatedInfiniteTupleEvent v := by
    filter_upwards [hm] with ω hω
    obtain ⟨v,hv⟩ := hω.exists_pairwise G k
    exact Set.mem_iUnion.mpr ⟨v,hv⟩
  have ho := (ae_iff_prob_eq_one (MeasurableSet.iUnion
    (fun v => G.measurableSet_separatedInfiniteTupleEvent v)).mem).mp he
  exact zero_ne_one (hn.symm.trans ho)

theorem exists_positive_encounter [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (p : unitInterval) (hp : 0<p) (o : V) (k : ℕ)
    (hm : ∀ᵐ ω ∂G.law p, G.infinitelyManyInfiniteClusters ω) :
    ∃ J : Set E, J.Finite ∧ 0<G.law p (G.encounterEvent J o k) := by
  obtain ⟨v,hv⟩ := G.exists_positive_separatedTuple p k hm
  obtain ⟨J,hJ,hconn⟩ := G.finite_bonds_connect_set hc o (Set.range v) (Set.finite_range v)
  refine ⟨J,hJ,?_⟩
  by_contra h
  have hz : G.law p (G.encounterEvent J o k)=0 := le_antisymm (le_of_not_gt h) bot_le
  have hn := BernoulliProduct.finite_union_preimage_null (fun _ : E => p) (fun _ => hp)
    J hJ (G.encounterEvent J o k) (G.measurableSet_encounterEvent J o k)
    (by simpa only [BernoulliProduct.law_const,law] using hz)
  have hn' : G.law p ((fun ω : Set E => J∪ω) ⁻¹' G.encounterEvent J o k)=0 := by
    simpa only [BernoulliProduct.law_const,law] using hn
  have hsub : G.separatedInfiniteTupleEvent v ⊆
      (fun ω : Set E => J∪ω) ⁻¹' G.encounterEvent J o k := by
    intro ω hω
    exact G.separatedTuple_force_encounter v J hJ o (fun i => hconn (v i) ⟨i,rfl⟩) ω hω
  exact hv.ne' (measure_mono_null hsub hn')

end CriticalPercolation.BondGraph
end
end

end OAI
