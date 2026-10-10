import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Density
import OAI.Probability.CriticalPercolation.Clusters.HitValue
import OAI.Probability.CriticalPercolation.Gluing.FiniteJointGluing

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

noncomputable def restrictVertices (U : Set V)
    (hU : ∀ e v, v ∈ G.ends e → v ∈ U) : BondGraph U E where
  ends e := (G.ends e).attachWith (hU e)

lemma restrictVertices_adj (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v w : U) :
    ((G.restrictVertices U hU).openGraph ω).Adj v w ↔
      (G.openGraph ω).Adj v.val w.val := by
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  constructor
  · rintro ⟨⟨e, he, hend⟩, hne⟩
    refine ⟨⟨e, he, ?_⟩, fun h => hne (Subtype.ext h)⟩
    have h := congrArg (Sym2.map Subtype.val) hend
    simpa only [restrictVertices, Sym2.attachWith_map_subtypeVal, Sym2.map_mk] using h
  · rintro ⟨⟨e, he, hend⟩, hne⟩
    refine ⟨⟨e, he, ?_⟩, fun h => hne (congrArg Subtype.val h)⟩
    apply Sym2.map.injective Subtype.val_injective
    simp only [restrictVertices, Sym2.attachWith_map_subtypeVal, Sym2.map_mk]
    exact hend

lemma restrictVertices_graph (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) :
    (G.restrictVertices U hU).openGraph ω = (G.openGraph ω).induce U := by
  ext v w
  exact G.restrictVertices_adj U hU ω v w

lemma adj_mem_support (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    {ω : Set E} {v w : V} (h : (G.openGraph ω).Adj v w) : v ∈ U ∧ w ∈ U := by
  obtain ⟨⟨e, _, he⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp h
  exact ⟨hU e v (by simp [he]), hU e w (by simp [he])⟩

lemma walk_support_subset (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    {ω : Set E} {v w : V} (p : (G.openGraph ω).Walk v w) (hv : v ∈ U) :
    ∀ u ∈ p.support, u ∈ U := by
  induction p with
  | nil => simpa
  | @cons v w z hvw p ih =>
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hv
      · exact ih (G.adj_mem_support U hU hvw).2 u hu

lemma cluster_subset_support (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    {ω : Set E} {v : V} (hv : v ∈ U) : G.cluster ω v ⊆ U := by
  rintro w ⟨p⟩
  exact G.walk_support_subset U hU p hv w p.end_mem_support

lemma restrictVertices_reachable (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v w : U) :
    ((G.restrictVertices U hU).openGraph ω).Reachable v w ↔
      (G.openGraph ω).Reachable v.val w.val := by
  rw [G.restrictVertices_graph]
  constructor
  · intro h
    exact h.map (SimpleGraph.Embedding.induce U).toHom
  · rintro ⟨p⟩
    exact ⟨p.induce U (G.walk_support_subset U hU p v.property)⟩

open CriticalPercolation.ClusterColumns CriticalPercolation.ClusterDeletion
open CriticalPercolation.FiniteProduct

lemma restrictVertices_hit_iff (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v : U) (A : Set V) :
    (component ((G.restrictVertices U hU).openGraph ω) v ∩ (Subtype.val ⁻¹' A)).Nonempty ↔
      (component (G.openGraph ω) v.val ∩ A).Nonempty := by
  constructor
  · rintro ⟨w, hw, hA⟩
    exact ⟨w.val, (G.restrictVertices_reachable U hU ω v w).mp hw, hA⟩
  · rintro ⟨w, hw, hA⟩
    have hwU := G.cluster_subset_support U hU v.property hw
    exact ⟨⟨w, hwU⟩, (G.restrictVertices_reachable U hU ω v ⟨w, hwU⟩).mpr hw, hA⟩

lemma restrictVertices_hitValue (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v : U) (A : Set V) :
    hitValue (Subtype.val ⁻¹' A) (component ((G.restrictVertices U hU).openGraph ω) v) =
      hitValue A (component (G.openGraph ω) v.val) := by
  simp only [hitValue, G.restrictVertices_hit_iff]

lemma restrictVertices_jointHitValue (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v : U) (A T : Set V) :
    jointHitValue (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' T)
        (component ((G.restrictVertices U hU).openGraph ω) v) =
      jointHitValue A T (component (G.openGraph ω) v.val) := by
  simp only [jointHitValue, G.restrictVertices_hit_iff]

lemma finite_edge_joint_gluing [Fintype E] (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (o : V) (A T : Set V) (hA : A.Finite) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ expect w
      (fun ω => hitValue T (component (G.openGraph ω) v))) :
    expect w (fun ω => hitValue A (component (G.openGraph ω) o)) * a ≤
      expect w (fun ω => jointHitValue A T (component (G.openGraph ω) o)) := by
  let U : Set V := insert o (A ∪ ⋃ e, (↑(G.ends e).toFinset : Set V))
  have hUf : U.Finite :=
    (hA.union (Set.finite_iUnion fun e => (G.ends e).toFinset.finite_toSet)).insert o
  let : Fintype U := hUf.fintype
  have hU : ∀ e v, v ∈ G.ends e → v ∈ U := by
    intro e v hv
    exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨e, by simpa using hv⟩))
  let R := G.restrictVertices U hU
  let o' : U := ⟨o, Set.mem_insert _ _⟩
  have h := R.finite_joint_gluing w hw hpos o' (Subtype.val ⁻¹' A)
    (Subtype.val ⁻¹' T) a (by
      intro v hv
      have heq : (fun ω : E → Prop =>
          hitValue (Subtype.val ⁻¹' T) (component (R.openGraph ω) v)) =
          (fun ω => hitValue T (component (G.openGraph ω) v.val)) := by
        funext ω
        exact G.restrictVertices_hitValue U hU ω v T
      rw [heq]
      exact ha v.val hv)
  have heq : (fun ω : E → Prop =>
      hitValue (Subtype.val ⁻¹' A) (component (R.openGraph ω) o')) =
      (fun ω => hitValue A (component (G.openGraph ω) o)) := by
    funext ω
    exact G.restrictVertices_hitValue U hU ω o' A
  have heq' : (fun ω : E → Prop =>
      jointHitValue (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' T)
        (component (R.openGraph ω) o')) =
      (fun ω => jointHitValue A T (component (G.openGraph ω) o)) := by
    funext ω
    exact G.restrictVertices_jointHitValue U hU ω o' A T
  rwa [heq, heq'] at h

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
