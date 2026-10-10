import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.SubexponentialVolumes
import OAI.Probability.CriticalPercolation.GraphGeometry.InfiniteAdjacent
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
import OAI.Probability.CriticalPercolation.Modular.ClusterDiscrepancy
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteInterpolationMeasure

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def distinctInfiniteEvent (x y : V) : Set (Set E) :=
  {ω | (G.cluster ω x).Infinite ∧ (G.cluster ω y).Infinite ∧
    ¬ (G.openGraph ω).Reachable x y}

lemma measurableSet_distinctInfiniteEvent [Countable V] [Countable E] (x y : V) :
    MeasurableSet (G.distinctInfiniteEvent x y) :=
  ((G.measurable_infinite_cluster x).and
    ((G.measurable_infinite_cluster y).and (G.measurable_reachable x y).not)).setOf

lemma distinctInfiniteEvent_subset_twoClusterEvent (x y : V) (s : ℕ) :
    G.distinctInfiniteEvent x y ⊆ G.twoClusterEvent x y s := by
  rintro ω ⟨hx,hy,hxy⟩
  exact ⟨⟨hxy,G.infiniteEvent_subset_clusterTail x s hx⟩,
    G.infiniteEvent_subset_clusterTail y s hy⟩

lemma cluster_insert_edge_unchanged (ω : Set E) (e : E) (o : V)
    (hends : ∀ v ∈ G.ends e, v ∉ G.cluster ω o) :
    G.cluster (insert e ω) o = G.cluster ω o := by
  apply Set.Subset.antisymm
  · intro y hy
    have hr := ((G.openGraph (insert e ω)).reachable_iff_reflTransGen o y).mp hy
    clear hy
    induction hr with
    | refl => exact .refl _
    | @tail x y hr hxy ih =>
      obtain ⟨⟨f,hf,hfe⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
      rcases hf with rfl | hf
      · exact False.elim (hends x (by simp [hfe]) ih)
      · have hadj : (G.openGraph ω).Adj x y :=
          (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨f,hf,hfe⟩,hne⟩
        exact ih.trans hadj.reachable
  · exact G.cluster_mono (Set.subset_insert e ω) o

lemma distinctInfinite_force_adjacent_length (n : ℕ) :
    ∀ (ω : Set E) (x y : V), lengthReach G.fullGraph n x y →
      ω ∈ G.distinctInfiniteEvent x y →
      ∃ S : Set E, S.Finite ∧ ∃ a b : V, G.fullGraph.Adj a b ∧
        S ∪ ω ∈ G.distinctInfiniteEvent a b := by
  induction n with
  | zero =>
    intro ω x y hxy h
    exact False.elim (h.2.2 (hxy ▸ SimpleGraph.Reachable.refl x))
  | succ n ih =>
    rintro ω x y ⟨u,hxu,huy⟩ ⟨hx,hy,hxy⟩
    by_cases hxuω : (G.openGraph ω).Reachable x u
    · refine ⟨∅,Set.finite_empty,u,y,huy,?_⟩
      rw [Set.empty_union]
      refine ⟨?_,hy,fun huy => hxy (hxuω.trans huy)⟩
      rwa [← G.cluster_eq_of_reachable hxuω]
    · obtain ⟨⟨e,_,he⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huy
      have hends : ∀ v ∈ G.ends e, v ∉ G.cluster ω x := by
        intro v hv
        rw [he,Sym2.mem_iff] at hv
        rcases hv with rfl | rfl
        · exact hxuω
        · exact hxy
      have hc := G.cluster_insert_edge_unchanged ω e x hends
      have hnewx : (G.cluster (insert e ω) x).Infinite := hc ▸ hx
      have hay : (G.openGraph (insert e ω)).Adj u y :=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,Set.mem_insert e ω,he⟩,hne⟩
      have hnewu : (G.cluster (insert e ω) u).Infinite := by
        have hh := hy.mono (G.cluster_mono (Set.subset_insert e ω) y)
        rwa [← G.cluster_eq_of_reachable hay.reachable] at hh
      have hnot : ¬ (G.openGraph (insert e ω)).Reachable x u := by
        change u ∉ G.cluster (insert e ω) x
        rwa [hc]
      obtain ⟨S,hS,a,b,hab,hhab⟩ := ih (insert e ω) x u hxu ⟨hnewx,hnewu,hnot⟩
      refine ⟨insert e S,hS.insert e,a,b,hab,?_⟩
      simpa only [Set.insert_union,Set.union_insert] using hhab

lemma distinctInfinite_force_adjacent (hconnected : G.fullGraph.Connected)
    (ω : Set E) (x y : V) (h : ω ∈ G.distinctInfiniteEvent x y) :
    ∃ S : Set E, S.Finite ∧ ∃ a b : V, G.fullGraph.Adj a b ∧
      S ∪ ω ∈ G.distinctInfiniteEvent a b := by
  obtain ⟨n,hn⟩ := (reachable_iff_exists_lengthReach G.fullGraph x y).mp (hconnected x y)
  exact G.distinctInfinite_force_adjacent_length n ω x y hn h

theorem adjacent_distinctInfinite_null [Countable V] [Countable E]
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (hg : G.SubexponentialGrowth)
    (p : unitInterval) (hp : (p:ℝ) ∈ Set.Ioo 0 1) (x y : V)
    (hxy : G.fullGraph.Adj x y) : G.law p (G.distinctInfiniteEvent x y) = 0 := by
  obtain ⟨A,_,hA⟩ := G.subexponential_adjacent_bound hconnected hlocal hquasi hg
  obtain ⟨⟨e,_,he⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
  have hbound : ∀ K : ℕ, (G.law p).real (G.distinctInfiniteEvent x y) ≤
      A/((p:ℝ)*(2:ℝ)^K) := by
    intro K
    have hsub := measureReal_mono (G.distinctInfiniteEvent_subset_twoClusterEvent x y (4^K))
      (μ := G.law p)
    have heq : s(x,y) = s((G.ends e).out.1,(G.ends e).out.2) := by
      exact he.symm.trans (G.ends e).out_eq.symm
    rw [G.twoClusterEvent_sym2 heq (4^K)] at hsub
    exact hsub.trans (hA p hp e K)
  have ht : Tendsto (fun K : ℕ => A/((p:ℝ)*(2:ℝ)^K)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).const_mul_atTop hp.1)
  have hz : (G.law p).real (G.distinctInfiniteEvent x y) = 0 :=
    le_antisymm (ge_of_tendsto ht (Eventually.of_forall hbound)) measureReal_nonneg
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hz

end CriticalPercolation.BondGraph
end
end
end

end OAI
