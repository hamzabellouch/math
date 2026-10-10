import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
import OAI.Probability.CriticalPercolation.ProductMeasure.TailProduct

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma cluster_union_subset (ω S : Set E) (o : V) :
    G.cluster (ω ∪ S) o ⊆ G.cluster ω o ∪
      ⋃ e ∈ S, ⋃ v ∈ (G.ends e).toFinset, G.cluster ω v := by
  intro z hz
  have hr := ((G.openGraph (ω ∪ S)).reachable_iff_reflTransGen o z).mp hz
  clear hz
  induction hr with
  | refl => exact Or.inl (.refl _)
  | @tail x y hr hxy ih =>
    obtain ⟨⟨e, he, heq⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
    rcases he with he | he
    · have hadj : (G.openGraph ω).Adj x y :=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,heq⟩,hne⟩
      rcases ih with ho | h
      · exact Or.inl (ho.trans hadj.reachable)
      · obtain ⟨f,hf,h⟩ := Set.mem_iUnion₂.mp h
        obtain ⟨v,hv,hh⟩ := Set.mem_iUnion₂.mp h
        exact Or.inr (Set.mem_iUnion₂.mpr ⟨f,hf,Set.mem_iUnion₂.mpr
          ⟨v,hv,hh.trans hadj.reachable⟩⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨e,he,Set.mem_iUnion₂.mpr
        ⟨y,by simp [heq], .refl _⟩⟩)

lemma percolates_union_finite_iff (ω S : Set E) (hS : S.Finite) :
    ω ∪ S ∈ G.percolates ↔ ω ∈ G.percolates := by
  constructor
  · rintro ⟨o,ho⟩
    by_contra hω
    have hfinite : ∀ v, (G.cluster ω v).Finite :=
      fun v => Set.not_infinite.mp (fun hv => hω ⟨v,hv⟩)
    exact ho (((hfinite o).union (hS.biUnion fun e _ =>
      (G.ends e).toFinset.finite_toSet.biUnion fun v _ => hfinite v)).subset
        (G.cluster_union_subset ω S o))
  · exact G.percolates_mono Set.subset_union_left

lemma percolates_diff_finite_iff (ω S : Set E) (hS : S.Finite) :
    ω \ S ∈ G.percolates ↔ ω ∈ G.percolates := by
  constructor
  · exact G.percolates_mono Set.sdiff_subset
  · intro hω
    have hh := G.percolates_mono (show ω ⊆ (ω \ S) ∪ S from
      fun e he => by by_cases hs : e ∈ S; exact Or.inr hs; exact Or.inl ⟨he,hs⟩) hω
    exact (G.percolates_union_finite_iff (ω \ S) S hS).mp hh

theorem percolates_zero_one [Countable V] [Countable E] (q : E → unitInterval) :
    BernoulliProduct.law q G.percolates = 0 ∨
      BernoulliProduct.law q G.percolates = 1 := by
  apply BernoulliProduct.zero_one_of_finite_erasure_invariant q G.percolates
    G.measurableSet_percolates
  intro S hS ω
  have heq : BernoulliProduct.forceOn S ∅ ω = ω \ S := by
    ext e
    change (if e ∈ S then False else e ∈ ω) ↔ (e ∈ ω ∧ e ∉ S)
    split_ifs <;> tauto
  rw [heq]
  exact G.percolates_diff_finite_iff ω S hS

lemma percolates_probability_one [Countable V] [Countable E] (p : unitInterval)
    (h : 0 < G.law p G.percolates) : G.law p G.percolates = 1 := by
  have hh := G.percolates_zero_one (fun _ => p)
  rw [BernoulliProduct.law_const] at hh
  exact hh.resolve_left (ne_of_gt h)

end CriticalPercolation.BondGraph
end
end
end

end OAI
