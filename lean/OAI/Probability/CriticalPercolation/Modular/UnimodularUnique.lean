import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.InfiniteUniqueness
import OAI.Probability.CriticalPercolation.Criticality.FiniteEnergy
import OAI.Probability.CriticalPercolation.Criticality.ParameterLeftBounds
import OAI.Probability.CriticalPercolation.Criticality.PositiveCritical
import OAI.Probability.CriticalPercolation.Criticality.SubcriticalLocalRateBound
import OAI.Probability.CriticalPercolation.Modular.UnimodularAdjacent

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma UnimodularRoot.critical_adjacent_bound (R : G.UnimodularRoot)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hpc : G.criticalProbability < 1)
    (e : E) : ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ,
      (G.law G.criticalProbability).real
        (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^k)) ≤
      A/((G.criticalProbability:ℝ)*(2:ℝ)^k) := by
  obtain ⟨A,hA,hbound⟩ := UnimodularRoot.subcritical_adjacent_bound G R hc hl e
  have hp : (0:ℝ) < G.criticalProbability :=
    G.criticalProbability_pos hc hl (UnimodularRoot.quasiTransitive G R)
  refine ⟨2*A,by positivity,?_⟩
  intro k
  have hb := G.twoCluster_bound_of_subcritical (G.ends e).out.1 (G.ends e).out.2 (4^k)
    G.criticalProbability hp (A/(2:ℝ)^k) (by positivity) (fun q hhalf hq => ?_)
  · convert hb using 1
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · have hq0 : (0:ℝ) < q := lt_of_lt_of_le (by linarith : (0:ℝ)<(G.criticalProbability:ℝ)/2) hhalf
    have hh := hbound q ⟨hq0,hq.trans hpc⟩ hq k
    convert hh using 1
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

lemma UnimodularRoot.critical_adjacent_distinctInfinite_null (R : G.UnimodularRoot)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hpc : G.criticalProbability < 1)
    (x y : V) (hxy : G.fullGraph.Adj x y) :
    G.law G.criticalProbability (G.distinctInfiniteEvent x y) = 0 := by
  obtain ⟨⟨e,_,he⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
  obtain ⟨A,_,hA⟩ := UnimodularRoot.critical_adjacent_bound G R hc hl hpc e
  have hp := G.criticalProbability_pos hc hl (UnimodularRoot.quasiTransitive G R)
  have hb (k : ℕ) : (G.law G.criticalProbability).real (G.distinctInfiniteEvent x y) ≤
      A/((G.criticalProbability:ℝ)*(2:ℝ)^k) := by
    have hs := measureReal_mono (G.distinctInfiniteEvent_subset_twoClusterEvent x y (4^k))
      (μ := G.law G.criticalProbability)
    have heq : s(x,y) = s((G.ends e).out.1,(G.ends e).out.2) := he.symm.trans (G.ends e).out_eq.symm
    rw [G.twoClusterEvent_sym2 heq (4^k)] at hs
    exact hs.trans (hA k)
  have ht : Tendsto (fun k : ℕ => A/((G.criticalProbability:ℝ)*(2:ℝ)^k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).const_mul_atTop hp)
  have hz : (G.law G.criticalProbability).real (G.distinctInfiniteEvent x y) = 0 :=
    le_antisymm (ge_of_tendsto ht (Eventually.of_forall hb)) measureReal_nonneg
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hz

lemma atMostOneInfinite_ae_of_adjacent_null (hc : G.fullGraph.Connected)
    (p : unitInterval) (hp : 0 < p)
    (hadj : ∀ x y, G.fullGraph.Adj x y → G.law p (G.distinctInfiniteEvent x y) = 0) :
    ∀ᵐ ω ∂G.law p, ω ∈ G.atMostOneInfinite := by
  have hn : ∀ (S : Finset E) (x y : V), ∀ᵐ ω ∂G.law p,
      G.fullGraph.Adj x y → (S : Set E) ∪ ω ∉ G.distinctInfiniteEvent x y := by
    intro S x y
    by_cases hxy : G.fullGraph.Adj x y
    · have hz := BernoulliProduct.finite_union_preimage_null (fun _ : E => p)
        (fun _ => hp) (S : Set E) S.finite_toSet (G.distinctInfiniteEvent x y)
        (G.measurableSet_distinctInfiniteEvent x y)
        (by rw [BernoulliProduct.law_const]; exact hadj x y hxy)
      rw [BernoulliProduct.law_const] at hz
      have hh : ∀ᵐ ω ∂G.law p, (S : Set E) ∪ ω ∉ G.distinctInfiniteEvent x y := by
        rw [ae_iff]
        simp only [not_not]
        exact hz
      exact hh.mono (fun _ h _ => h)
    · exact Eventually.of_forall (fun _ h => False.elim (hxy h))
  have hall := ae_all_iff.mpr (fun S => ae_all_iff.mpr (fun x => ae_all_iff.mpr (hn S x)))
  filter_upwards [hall] with ω hω
  intro x y hx hy
  by_contra hxy
  obtain ⟨S,hS,a,b,hab,hh⟩ := G.distinctInfinite_force_adjacent hc ω x y ⟨hx,hy,hxy⟩
  exact hω hS.toFinset a b hab (by simpa only [Set.Finite.coe_toFinset] using hh)

theorem UnimodularRoot.critical_atMostOneInfinite_ae (R : G.UnimodularRoot)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hpc : G.criticalProbability < 1) :
    ∀ᵐ ω ∂G.law G.criticalProbability, ω ∈ G.atMostOneInfinite :=
  G.atMostOneInfinite_ae_of_adjacent_null hc G.criticalProbability
    (G.criticalProbability_pos hc hl (UnimodularRoot.quasiTransitive G R))
    (UnimodularRoot.critical_adjacent_distinctInfinite_null G R hc hl hpc)

omit [Countable V] [Countable E] in

theorem UnimodularRoot.exponential_critical_null (R : G.UnimodularRoot)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hpc : G.criticalProbability < 1)
    (o : V) (γ : ℝ) (hγ : 0 < γ) (N : ℕ)
    (hgrowth : ∀ m≥N, ∀ v : V, γ*m ≤ Real.log ((G.vertexBall v m).ncard : ℝ)) :
    G.law G.criticalProbability G.percolates = 0 := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  exact Sharpness.critical_null_of_unique G hc hl (UnimodularRoot.quasiTransitive G R)
    o γ hγ N hgrowth (UnimodularRoot.critical_atMostOneInfinite_ae G R hc hl hpc)

end CriticalPercolation.BondGraph
end
end

end OAI
