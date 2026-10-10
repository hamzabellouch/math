import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.FiniteEnergy
import OAI.Probability.CriticalPercolation.Clusters.InfiniteUniquenessGeometry
import OAI.Probability.CriticalPercolation.Clusters.PercolationTail

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def atMostOneInfinite : Set (Set E) :=
  {ω | ∀ x y, (G.cluster ω x).Infinite → (G.cluster ω y).Infinite →
    (G.openGraph ω).Reachable x y}

lemma measurableSet_atMostOneInfinite : MeasurableSet G.atMostOneInfinite := by
  have heq : G.atMostOneInfinite = ⋂ x, ⋂ y, (G.distinctInfiniteEvent x y)ᶜ := by
    ext ω
    simp only [atMostOneInfinite,distinctInfiniteEvent,Set.mem_ofPred_eq,Set.mem_iInter,
      Set.mem_compl_iff]
    constructor
    · intro h x y hh
      exact hh.2.2 (h x y hh.1 hh.2.1)
    · intro h x y hx hy
      by_contra hr
      exact h x y ⟨hx,hy,hr⟩
  rw [heq]
  exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
    (G.measurableSet_distinctInfiniteEvent x y).compl

theorem atMostOneInfinite_ae (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive)
    (hg : G.SubexponentialGrowth) (p : unitInterval)
    (hp : (p:ℝ) ∈ Set.Ioo 0 1) : ∀ᵐ ω ∂G.law p, ω ∈ G.atMostOneInfinite := by
  have hn : ∀ (S : Finset E) (x y : V), ∀ᵐ ω ∂G.law p,
      G.fullGraph.Adj x y → (S : Set E) ∪ ω ∉ G.distinctInfiniteEvent x y := by
    intro S x y
    by_cases hxy : G.fullGraph.Adj x y
    · have hz := BernoulliProduct.finite_union_preimage_null (fun _ : E => p)
        (fun _ => hp.1) (S : Set E) S.finite_toSet (G.distinctInfiniteEvent x y)
        (G.measurableSet_distinctInfiniteEvent x y)
        (by rw [BernoulliProduct.law_const];
            exact G.adjacent_distinctInfinite_null hconnected hlocal hquasi hg p hp x y hxy)
      rw [BernoulliProduct.law_const] at hz
      have hh : ∀ᵐ ω ∂G.law p, (S : Set E) ∪ ω ∉ G.distinctInfiniteEvent x y := by
        rw [ae_iff]
        simp only [not_not]
        exact hz
      exact hh.mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hxy h))
  have hall := ae_all_iff.mpr (fun S => ae_all_iff.mpr (fun x => ae_all_iff.mpr (hn S x)))
  filter_upwards [hall] with ω hω
  intro x y hx hy
  by_contra hxy
  obtain ⟨S,hS,a,b,hab,hh⟩ := G.distinctInfinite_force_adjacent hconnected ω x y ⟨hx,hy,hxy⟩
  have hnot := hω hS.toFinset a b hab
  exact hnot (by simpa only [Set.Finite.coe_toFinset] using hh)

theorem uniqueInfinite_ae (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive)
    (hg : G.SubexponentialGrowth) (p : unitInterval)
    (hp : (p:ℝ) ∈ Set.Ioo 0 1) (hpositive : 0 < G.law p G.percolates) :
    ∀ᵐ ω ∂G.law p, ∃ x, (G.cluster ω x).Infinite ∧
      ∀ y, (G.cluster ω y).Infinite → (G.openGraph ω).Reachable x y := by
  have hex : ∀ᵐ ω ∂G.law p, ω ∈ G.percolates := by
    rw [ae_iff]
    change G.law p G.percolatesᶜ = 0
    rw [measure_compl G.measurableSet_percolates (measure_ne_top _ _),
      G.percolates_probability_one p hpositive, measure_univ, tsub_self]
  filter_upwards [hex,G.atMostOneInfinite_ae hconnected hlocal hquasi hg p hp] with ω hω hu
  obtain ⟨x,hx⟩ := hω
  exact ⟨x,hx,fun y hy => hu x y hx hy⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
