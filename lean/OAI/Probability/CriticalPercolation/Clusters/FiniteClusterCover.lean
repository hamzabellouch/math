import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
import OAI.Probability.CriticalPercolation.Clusters.PercolationTail
import OAI.Probability.CriticalPercolation.Clusters.InfiniteUniqueness

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def infiniteClusterCover (ω : Set E) (S : Set V) : Prop :=
  ∀ v, (G.cluster ω v).Infinite → ∃ s ∈ S, (G.openGraph ω).Reachable v s

lemma measurable_infiniteClusterCover [Countable V] [Countable E] (S : Set V) :
    Measurable (fun ω => G.infiniteClusterCover ω S) := by
  unfold infiniteClusterCover
  exact .forall fun v => (G.measurable_infinite_cluster v).imp
    (.exists fun s => measurable_const.and (G.measurable_reachable v s))

lemma infinite_cluster_union_has_old (ω J : Set E) (hJ : J.Finite) (o : V)
    (ho : (G.cluster (ω ∪ J) o).Infinite) :
    ∃ v, (G.openGraph (ω ∪ J)).Reachable o v ∧ (G.cluster ω v).Infinite := by
  by_contra h
  have hf (v : V) (hv : (G.openGraph (ω ∪ J)).Reachable o v) :
      (G.cluster ω v).Finite := by
    apply Set.not_infinite.mp
    intro hi
    exact h ⟨v,hv,hi⟩
  have hσ (v : V) : (G.cluster ω v ∩ G.cluster (ω ∪ J) o).Finite := by
    by_cases hv : (G.openGraph (ω ∪ J)).Reachable o v
    · exact (hf v hv).inter_of_left _
    · have he : G.cluster ω v ∩ G.cluster (ω ∪ J) o = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx,hox⟩
        exact hv (hox.trans (G.cluster_mono Set.subset_union_left v hx).symm)
      rw [he]
      exact Set.finite_empty
  apply ho
  apply ((hf o (.refl _)).union (hJ.biUnion fun e _ =>
      (G.ends e).toFinset.finite_toSet.biUnion fun v _ => hσ v)).subset
  intro z hz
  rcases G.cluster_union_subset ω J o hz with hh | hh
  · exact Or.inl hh
  · obtain ⟨e,he,hh⟩ := Set.mem_iUnion₂.mp hh
    obtain ⟨v,hv,hvz⟩ := Set.mem_iUnion₂.mp hh
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨e,he,Set.mem_iUnion₂.mpr ⟨v,hv,hvz,hz⟩⟩)

lemma finite_bonds_connect_set (hc : G.fullGraph.Connected) (o : V)
    (S : Set V) (hS : S.Finite) :
    ∃ J : Set E, J.Finite ∧ ∀ s ∈ S, (G.openGraph J).Reachable o s := by
  obtain ⟨J,hJ,_,hconn⟩ := G.finite_subset_cluster_finite_witness hS
    (show S ⊆ G.cluster Set.univ o from fun s _ => hc o s)
  exact ⟨J,hJ,fun s hs => hconn hs⟩

lemma atMostOneInfinite_union_of_cover (ω J : Set E) (hJ : J.Finite)
    (o : V) (S : Set V) (hconn : ∀ s ∈ S, (G.openGraph J).Reachable o s)
    (hcover : G.infiniteClusterCover ω S) : ω ∪ J ∈ G.atMostOneInfinite := by
  have hroot (x : V) (hx : (G.cluster (ω ∪ J) x).Infinite) :
      (G.openGraph (ω ∪ J)).Reachable x o := by
    obtain ⟨v,hxv,hv⟩ := G.infinite_cluster_union_has_old ω J hJ x hx
    obtain ⟨s,hs,hvs⟩ := hcover v hv
    exact hxv.trans ((G.cluster_mono Set.subset_union_left v hvs).trans
      (G.cluster_mono Set.subset_union_right o (hconn s hs)).symm)
  intro x y hx hy
  exact (hroot x hx).trans (hroot y hy).symm

end CriticalPercolation.BondGraph
end
end

end OAI
