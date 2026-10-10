import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
import OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphIso
import OAI.Probability.CriticalPercolation.Criticality.FiniteEnergy
import OAI.Probability.CriticalPercolation.Clusters.InfiniteUniquenessGeometry
import OAI.Probability.CriticalPercolation.Modular.HeavyClusterNumber

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def distinctHeavyEvent (o x y : V) : Set (Set E) :=
  {ω | G.modularMass o (G.cluster ω x)=∞ ∧ G.modularMass o (G.cluster ω y)=∞ ∧
    ¬(G.openGraph ω).Reachable x y}

lemma measurableSet_distinctHeavyEvent [Countable V] [Countable E] (o x y : V) :
    MeasurableSet (G.distinctHeavyEvent o x y) :=
  ((G.measurable_modularClusterMass o x).eq_const ∞).and
    (((G.measurable_modularClusterMass o y).eq_const ∞).and (G.measurable_reachable x y).not) |>.setOf

lemma Aut.distinctHeavyEvent_image_iff (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (φ : G.Aut) (o x y : V) (ω : Set E) :
    φ.edge '' ω ∈ G.distinctHeavyEvent o (φ.vertex x) (φ.vertex y) ↔
      ω∈G.distinctHeavyEvent o x y := by
  have hi (v : V) : G.modularMass o (G.cluster (φ.edge '' ω) (φ.vertex v))=∞ ↔
      G.modularMass o (G.cluster ω v)=∞ := by
    rw [G.modularMass_eq_top_change_base hc hl o (φ.vertex o),←φ.cluster_image,φ.modularMass_image]
  exact and_congr (hi x) (and_congr (hi y)
    (not_congr (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω) (u := x) (v := y))))

lemma Aut.distinctHeavyEvent_measure [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (φ : G.Aut) (p : unitInterval) (o x y : V) :
    G.law p (G.distinctHeavyEvent o (φ.vertex x) (φ.vertex y))=
      G.law p (G.distinctHeavyEvent o x y) := by
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_distinctHeavyEvent _ _ _)]
  congr 1
  ext ω
  exact φ.distinctHeavyEvent_image_iff G hc hl o x y ω

lemma distinctHeavy_force_adjacent_length (o : V) (n : ℕ) :
    ∀ (ω : Set E) (x y : V), lengthReach G.fullGraph n x y →
      ω∈G.distinctHeavyEvent o x y →
      ∃ S : Set E, S.Finite ∧ ∃ a b : V, G.fullGraph.Adj a b ∧
        S∪ω∈G.distinctHeavyEvent o a b := by
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
      rwa [←G.cluster_eq_of_reachable hxuω]
    · obtain ⟨⟨e,_,he⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huy
      have hends : ∀ v∈G.ends e, v∉G.cluster ω x := by
        intro v hv
        rw [he,Sym2.mem_iff] at hv
        rcases hv with rfl|rfl
        · exact hxuω
        · exact hxy
      have hc := G.cluster_insert_edge_unchanged ω e x hends
      have hnewx : G.modularMass o (G.cluster (insert e ω) x)=∞ := hc ▸ hx
      have hay : (G.openGraph (insert e ω)).Adj u y :=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,Set.mem_insert e ω,he⟩,hne⟩
      have hnewu : G.modularMass o (G.cluster (insert e ω) u)=∞ := by
        have hh : G.modularMass o (G.cluster (insert e ω) y)=∞ :=
          top_unique (hy ▸ G.modularMass_mono o (G.cluster_mono (Set.subset_insert e ω) y))
        rwa [←G.cluster_eq_of_reachable hay.reachable] at hh
      have hnot : ¬(G.openGraph (insert e ω)).Reachable x u := by
        change u∉G.cluster (insert e ω) x
        rwa [hc]
      obtain ⟨S,hS,a,b,hab,hhab⟩ := ih (insert e ω) x u hxu ⟨hnewx,hnewu,hnot⟩
      refine ⟨insert e S,hS.insert e,a,b,hab,?_⟩
      simpa only [Set.insert_union,Set.union_insert] using hhab

lemma distinctHeavy_force_adjacent (hc : G.fullGraph.Connected) (o : V)
    (ω : Set E) (x y : V) (h : ω∈G.distinctHeavyEvent o x y) :
    ∃ S : Set E, S.Finite ∧ ∃ a b : V, G.fullGraph.Adj a b ∧
      S∪ω∈G.distinctHeavyEvent o a b := by
  obtain ⟨n,hn⟩ := (reachable_iff_exists_lengthReach G.fullGraph x y).mp (hc x y)
  exact G.distinctHeavy_force_adjacent_length o n ω x y hn h

lemma atMostOneHeavy_ae_of_adjacent_null [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (p : unitInterval) (hp : 0<(p:ℝ)) (o : V)
    (hnull : ∀ x y, G.fullGraph.Adj x y → G.law p (G.distinctHeavyEvent o x y)=0) :
    ∀ᵐ ω ∂G.law p, ω∈G.atMostOneHeavy o := by
  have hn : ∀ (S : Finset E) (x y : V), ∀ᵐ ω ∂G.law p,
      G.fullGraph.Adj x y → (S : Set E)∪ω∉G.distinctHeavyEvent o x y := by
    intro S x y
    by_cases hxy : G.fullGraph.Adj x y
    · have hz := BernoulliProduct.finite_union_preimage_null (fun _ : E => p)
        (fun _ => hp) (S : Set E) S.finite_toSet (G.distinctHeavyEvent o x y)
        (G.measurableSet_distinctHeavyEvent o x y)
        (by rw [BernoulliProduct.law_const]; exact hnull x y hxy)
      rw [BernoulliProduct.law_const] at hz
      have hh : ∀ᵐ ω ∂G.law p, (S : Set E)∪ω∉G.distinctHeavyEvent o x y := by
        rw [ae_iff]
        simp only [not_not]
        exact hz
      exact hh.mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hxy h))
  have hall := ae_all_iff.mpr (fun S => ae_all_iff.mpr (fun x => ae_all_iff.mpr (hn S x)))
  filter_upwards [hall] with ω hω
  intro x y hx hy
  by_contra hxy
  obtain ⟨S,hS,a,b,hab,hh⟩ := G.distinctHeavy_force_adjacent hc o ω x y ⟨hx,hy,hxy⟩
  have hnot := hω hS.toFinset a b hab
  exact hnot (by simpa only [Set.Finite.coe_toFinset] using hh)

end CriticalPercolation.BondGraph
end
end

end OAI
