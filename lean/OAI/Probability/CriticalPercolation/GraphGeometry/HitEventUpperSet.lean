import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteOpenWitness

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
lemma hitEvent_isUpperSet (o : V) (A : Set V) : IsUpperSet (G.hitEvent o A) :=
  fun _ _ h => G.hitEvent_mono_edges o A h

lemma hitEvent_hasFiniteOpenWitness (o : V) (A : Set V) :
    BernoulliProduct.HasFiniteOpenWitness (G.hitEvent o A) := by
  rintro ω ⟨v, hv, hvA⟩
  obtain ⟨s, hs, hsω, hvs⟩ := G.mem_cluster_finite_witness hv
  exact ⟨s, hs, hsω, v, hvs, hvA⟩

lemma lowerSemicontinuous_real_hitEvent [Countable E] (o : V) (A : Set V) :
    LowerSemicontinuous (fun p : unitInterval => (G.law p).real (G.hitEvent o A)) := by
  simpa [law, BernoulliProduct.law_const] using
    BernoulliProduct.lowerSemicontinuous_real_finiteWitness (G.hitEvent o A)
      (G.hitEvent_isUpperSet o A) (G.hitEvent_hasFiniteOpenWitness o A)
end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
