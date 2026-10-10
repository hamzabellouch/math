import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.ProductMeasure.BitMeasure
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma measurable_image_equiv (e : E ≃ E) :
    Measurable (fun ω : Set E => e '' ω) := by
  have he : (fun ω : Set E => e '' ω) = (fun ω => e.symm ⁻¹' ω) := by
    funext ω
    ext i
    simp
  rw [he]
  exact Measurable.of_eval (fun index => measurable_set_mem (e.symm index))

lemma law_map_equiv (p : unitInterval) (e : E ≃ E) :
    (law (fun _ : E => p)).map (fun ω : Set E => e '' ω) = law (fun _ : E => p) := by
  unfold law
  rw [Measure.map_map (measurable_image_equiv e) MeasurableEquiv.setOfPred.measurable]
  have he : (fun ω : Set E => e '' ω) ∘ MeasurableEquiv.setOfPred =
      MeasurableEquiv.setOfPred ∘ MeasurableEquiv.piCongrLeft (fun _ : E => Prop) e := by
    funext ω
    ext i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [he, ← Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    Measure.infinitePi_map_piCongrLeft (fun _ : E => bitMeasure p) e]

lemma real_law_subset (p : unitInterval) (s : Set E) (hs : s.Finite) :
    (law (fun _ : E => p)).real {ω | s ⊆ ω} = (p : ℝ) ^ s.ncard := by
  let : Fintype s := hs.fintype
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  have he : {ω : Set E | s ⊆ ω} =
      (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹' {Set.univ} := by
    ext ω
    simp [Set.subset_def, Set.eq_univ_iff_forall]
  rw [he, measureReal_def, ← Measure.map_apply hmeas (.of_discrete),
    law_map_restrict, law_const]
  change (setBernoulli (Set.univ : Set s) p).real {Set.univ} = _
  rw [setBernoulli_real_singleton p (Subset.rfl) Set.finite_univ]
  simp [Set.ncard_univ]

end CriticalPercolation.BernoulliProduct
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

instance law_probability (p : unitInterval) : IsProbabilityMeasure (G.law p) := by
  unfold law
  infer_instance

lemma Aut.adj_map (φ : G.Aut) (ω : Set E) (v w : V) :
    (G.openGraph (φ.edge '' ω)).Adj (φ.vertex v) (φ.vertex w) ↔
      (G.openGraph ω).Adj v w := by
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  constructor
  · rintro ⟨⟨e, ⟨f, hf, rfl⟩, hend⟩, hne⟩
    rw [φ.preserves, ← Sym2.map_mk] at hend
    exact ⟨⟨f, hf, Sym2.map.injective φ.vertex.injective hend⟩,
      fun h => hne (congrArg φ.vertex h)⟩
  · rintro ⟨⟨e, he, hend⟩, hne⟩
    refine ⟨⟨φ.edge e, ⟨e, he, rfl⟩, ?_⟩, ?_⟩
    · rw [φ.preserves, hend, Sym2.map_mk]
    · exact fun h => hne (φ.vertex.injective h)

noncomputable def Aut.openGraphIso (φ : G.Aut) (ω : Set E) :
    G.openGraph ω ≃g G.openGraph (φ.edge '' ω) where
  toEquiv := φ.vertex
  map_rel_iff' := fun {v w} => Aut.adj_map G φ ω v w

lemma Aut.cluster_image (φ : G.Aut) (ω : Set E) (o : V) :
    φ.vertex '' G.cluster ω o = G.cluster (φ.edge '' ω) (φ.vertex o) := by
  ext v
  obtain ⟨w, rfl⟩ := φ.vertex.surjective v
  simp only [Set.mem_image, φ.vertex.injective.eq_iff, exists_eq_right]
  change (G.openGraph ω).Reachable o w ↔
    (G.openGraph (φ.edge '' ω)).Reachable (φ.vertex o) (φ.vertex w)
  exact (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω) (u := o) (v := w)).symm

def infiniteEvent (o : V) : Set (Set E) := {ω | (G.cluster ω o).Infinite}

lemma measurableSet_infiniteEvent [Countable V] [Countable E] (o : V) :
    MeasurableSet (G.infiniteEvent o) := (G.measurable_infinite_cluster o).setOf

lemma Aut.preimage_infiniteEvent (φ : G.Aut) (o : V) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' (G.infiniteEvent (φ.vertex o)) =
      G.infiniteEvent o := by
  ext ω
  change (G.cluster (φ.edge '' ω) (φ.vertex o)).Infinite ↔ (G.cluster ω o).Infinite
  rw [← φ.cluster_image]
  exact Set.infinite_image_iff φ.vertex.injective.injOn

lemma law_map_aut (p : unitInterval) (φ : G.Aut) :
    (G.law p).map (fun ω : Set E => φ.edge '' ω) = G.law p := by
  simpa only [BernoulliProduct.law_const, law] using
    BernoulliProduct.law_map_equiv p φ.edge

lemma Aut.infiniteEvent_measure [Countable V] [Countable E]
    (φ : G.Aut) (p : unitInterval) (o : V) :
    G.law p (G.infiniteEvent (φ.vertex o)) = G.law p (G.infiniteEvent o) := by
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_infiniteEvent _), φ.preimage_infiniteEvent]

lemma Aut.infiniteEvent_real [Countable V] [Countable E]
    (φ : G.Aut) (p : unitInterval) (o : V) :
    (G.law p).real (G.infiniteEvent (φ.vertex o)) = (G.law p).real (G.infiniteEvent o) := by
  simp only [measureReal_def, φ.infiniteEvent_measure]

end CriticalPercolation.BondGraph

open Filter Topology

end
end

end OAI
