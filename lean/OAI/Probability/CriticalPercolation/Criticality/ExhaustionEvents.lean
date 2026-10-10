import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.HitEventUpperSet
import OAI.Probability.CriticalPercolation.ProductMeasure.MeasurableSetRestrict
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteInterpolationMeasure

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation
namespace BernoulliProduct
variable {E : Type*} [Countable E]

lemma tendsto_real_sdiff_finiteWitness (p : unitInterval) (A B : Set (Set E))
    (hAm : IsUpperSet A) (hBm : IsUpperSet B)
    (hA : HasFiniteOpenWitness A) (hB : HasFiniteOpenWitness B)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (law (fun _ : E => p)).real {ω | K n ∩ ω ∈ A \ B})
      atTop (𝓝 ((law (fun _ : E => p)).real (A \ B))) := by
  have hAB := hA.inter hB hAm hBm
  have hABm : IsUpperSet (A∩B) := fun _ _ h hh => ⟨hAm h hh.1,hBm h hh.2⟩
  have h1 := tendsto_real_finiteWitness p A hAm hA K
  have h2 := tendsto_real_finiteWitness p (A∩B) hABm hAB K
  have he (n : ℕ) : (law (fun _ : E => p)).real {ω | K n ∩ ω ∈ A \ B} =
      (law (fun _ : E => p)).real {ω | K n ∩ ω ∈ A} -
        (law (fun _ : E => p)).real {ω | K n ∩ ω ∈ A∩B} := by
    exact eq_sub_iff_add_eq.mpr (measureReal_sdiff_add_inter
      (measurableSet_restrict (K n) (K.finite n) B))
  have he' : (law (fun _ : E => p)).real (A \ B) =
      (law (fun _ : E => p)).real A - (law (fun _ : E => p)).real (A∩B) := by
    exact eq_sub_iff_add_eq.mpr (measureReal_sdiff_add_inter
      (measurableSet_finiteWitness B hBm hB))
  simp_rw [he,he']
  exact h1.sub h2

end BernoulliProduct
namespace BondGraph
variable {V E : Type*} [Countable E] (G : BondGraph V E)

omit [Countable E] in
lemma twoClusterEvent_sdiff (u v : V) (s : ℕ) :
    G.twoClusterEvent u v s = (G.clusterTail u s ∩ G.clusterTail v s) \ G.hitEvent u {v} := by
  ext ω
  simp only [twoClusterEvent,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_sdiff,
    hitEvent,Set.inter_singleton_nonempty,cluster]
  tauto

lemma tendsto_real_twoCluster_restrict (p : unitInterval) (u v : V) (s : ℕ)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (G.law p).real {ω | K n ∩ ω ∈ G.twoClusterEvent u v s})
      atTop (𝓝 ((G.law p).real (G.twoClusterEvent u v s))) := by
  rw [G.twoClusterEvent_sdiff]
  simp only [law,← BernoulliProduct.law_const]
  apply BernoulliProduct.tendsto_real_sdiff_finiteWitness
  · exact fun _ _ h hh => ⟨G.clusterTail_isUpperSet u s h hh.1,
      G.clusterTail_isUpperSet v s h hh.2⟩
  · exact G.hitEvent_isUpperSet u {v}
  · exact (G.clusterTail_hasFiniteOpenWitness u s).inter
      (G.clusterTail_hasFiniteOpenWitness v s) (G.clusterTail_isUpperSet u s)
      (G.clusterTail_isUpperSet v s)
  · exact G.hitEvent_hasFiniteOpenWitness u {v}

omit [Countable E] in
lemma tendsto_real_reachable_restrict (p : unitInterval) (u v : V)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (G.law p).real {ω | (G.openGraph (K n ∩ ω)).Reachable u v})
      atTop (𝓝 ((G.law p).real {ω | (G.openGraph ω).Reachable u v})) := by
  have hh := BernoulliProduct.tendsto_real_finiteWitness p (G.hitEvent u {v})
    (G.hitEvent_isUpperSet u {v}) (G.hitEvent_hasFiniteOpenWitness u {v}) K
  simpa only [law,← BernoulliProduct.law_const,hitEvent,Set.inter_singleton_nonempty,
    cluster,Set.mem_ofPred_eq] using hh

end BondGraph
end CriticalPercolation
end
end
end

end OAI
