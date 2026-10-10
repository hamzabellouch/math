import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphIso
import OAI.Probability.CriticalPercolation.Criticality.FiniteEnergy
import OAI.Probability.CriticalPercolation.Clusters.FiniteClusterCover
import OAI.Probability.CriticalPercolation.Clusters.GraphErgodicity

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.atMostOneInfinite_image_iff (φ : G.Aut) (ω : Set E) :
    φ.edge '' ω ∈ G.atMostOneInfinite ↔ ω ∈ G.atMostOneInfinite := by
  have hi (x : V) : (G.cluster (φ.edge '' ω) (φ.vertex x)).Infinite ↔
      (G.cluster ω x).Infinite := by
    rw [←φ.cluster_image]
    exact Set.infinite_image_iff φ.vertex.injective.injOn
  have hr (x y : V) := SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)
    (u := x) (v := y)
  constructor
  · intro h x y hx hy
    exact (hr x y).mp (h (φ.vertex x) (φ.vertex y) ((hi x).mpr hx) ((hi y).mpr hy))
  · intro h x y hx hy
    obtain ⟨a,rfl⟩ := φ.vertex.surjective x
    obtain ⟨b,rfl⟩ := φ.vertex.surjective y
    exact (hr a b).mpr (h a b ((hi a).mp hx) ((hi b).mp hy))

lemma atMostOneInfinite_zero_one [Infinite V] [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) : G.law p G.atMostOneInfinite = 0 ∨
      G.law p G.atMostOneInfinite = 1 :=
  G.invariant_event_zero_one hc hl hq p G.atMostOneInfinite G.measurableSet_atMostOneInfinite
    (fun φ => Set.ext fun ω => Aut.atMostOneInfinite_image_iff G φ ω)

lemma no_finite_infiniteClusterCover_ae_of_unique_null [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (p : unitInterval) (hp : (0:ℝ) < p)
    (hnull : G.law p G.atMostOneInfinite = 0) :
    ∀ᵐ ω ∂G.law p, ∀ S : Finset V, ¬ G.infiniteClusterCover ω (S : Set V) := by
  apply ae_all_iff.mpr
  intro S
  obtain ⟨o⟩ := hc.nonempty
  obtain ⟨J,hJ,hconn⟩ := G.finite_bonds_connect_set hc o (S : Set V) S.finite_toSet
  have hn := BernoulliProduct.finite_union_preimage_null (fun _ : E => p) (fun _ => hp)
    J hJ G.atMostOneInfinite G.measurableSet_atMostOneInfinite
    (by simpa only [BernoulliProduct.law_const,law] using hnull)
  have hn' : G.law p ((fun ω : Set E => J ∪ ω) ⁻¹' G.atMostOneInfinite) = 0 := by
    simpa only [BernoulliProduct.law_const,law] using hn
  rw [ae_iff]
  apply measure_mono_null _ hn'
  intro ω hω
  change J ∪ ω ∈ G.atMostOneInfinite
  rw [Set.union_comm]
  exact G.atMostOneInfinite_union_of_cover ω J hJ o (S : Set V) hconn (not_not.mp hω)

def infinitelyManyInfiniteClusters (ω : Set E) : Prop :=
  ∀ S : Finset V, ∃ v, (G.cluster ω v).Infinite ∧
    ∀ s ∈ S, ¬ (G.openGraph ω).Reachable v s

lemma infinitelyManyInfiniteClusters_iff_no_finite_cover (ω : Set E) :
    G.infinitelyManyInfiniteClusters ω ↔
      ∀ S : Finset V, ¬ G.infiniteClusterCover ω (S : Set V) := by
  simp only [infinitelyManyInfiniteClusters,infiniteClusterCover]
  push Not
  rfl

theorem unique_or_infinitely_many_ae [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : (0:ℝ) < p) :
    (∀ᵐ ω ∂G.law p, ω ∈ G.atMostOneInfinite) ∨
    (∀ᵐ ω ∂G.law p, G.infinitelyManyInfiniteClusters ω) := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  rcases G.atMostOneInfinite_zero_one hc hl hq p with hz | ho
  · right
    filter_upwards [G.no_finite_infiniteClusterCover_ae_of_unique_null hc p hp hz] with ω hω
    exact (G.infinitelyManyInfiniteClusters_iff_no_finite_cover ω).mpr hω
  · left
    rw [ae_iff]
    change G.law p G.atMostOneInfiniteᶜ = 0
    rw [measure_compl G.measurableSet_atMostOneInfinite (measure_ne_top _ _),ho,
      measure_univ,tsub_self]

end CriticalPercolation.BondGraph
end
end

end OAI
