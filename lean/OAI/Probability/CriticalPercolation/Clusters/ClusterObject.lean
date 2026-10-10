import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
import OAI.Probability.CriticalPercolation.ProductMeasure.Distribution

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct
open scoped Classical

variable {V E : Type*} (G : BondGraph V E)

abbrev ClusterObject (V E : Type*) := Set V × Set E

def clusterObject (ω : Set E) (S : Set V) : ClusterObject V E :=
  (roots (G.openGraph ω) S, ω ∩ G.incidentEdges (roots (G.openGraph ω) S))

def eraseVertices (ω : Set E) (U : Set V) : Set E := ω \ G.incidentEdges U

lemma incidentEdges_mono {S T : Set V} (h : S ⊆ T) : G.incidentEdges S ⊆ G.incidentEdges T := by
  rintro e ⟨v, hv, he⟩
  exact ⟨v, h hv, he⟩

lemma clusterObject_mono {ω ω' : Set E} (h : ω ⊆ ω') (S : Set V) :
    G.clusterObject ω S ≤ G.clusterObject ω' S := by
  have hr := roots_mono (SimpleGraph.fromEdgeSet_mono (Set.image_mono (f := G.ends) h)) S
  exact ⟨hr, fun _ he => ⟨h he.1, G.incidentEdges_mono hr he.2⟩⟩

lemma eraseVertices_mono {ω ω' : Set E} (h : ω ⊆ ω') (U : Set V) :
    G.eraseVertices ω U ⊆ G.eraseVertices ω' U :=
  fun _ he => ⟨h he.1, he.2⟩

lemma eraseVertices_antitone {U U' : Set V} (h : U ⊆ U') (ω : Set E) :
    G.eraseVertices ω U' ⊆ G.eraseVertices ω U :=
  fun _ he => ⟨he.1, fun hh => he.2 (G.incidentEdges_mono h hh)⟩

lemma openGraph_eraseVertices (ω : Set E) (U : Set V) :
    G.openGraph (G.eraseVertices ω U) = delete (G.openGraph ω) U := by
  ext v w
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image,
    eraseVertices, Set.mem_sdiff, delete]
  constructor
  · rintro ⟨⟨e, ⟨he, hU⟩, heq⟩, hne⟩
    refine ⟨⟨⟨e, he, heq⟩, hne⟩, ?_, ?_⟩
    · intro hv
      exact hU ⟨v, hv, by simp [heq]⟩
    · intro hw
      exact hU ⟨w, hw, by simp [heq]⟩
  · rintro ⟨⟨⟨e, he, heq⟩, hne⟩, hv, hw⟩
    refine ⟨⟨e, ⟨he, ?_⟩, heq⟩, hne⟩
    rintro ⟨t, ht, hte⟩
    rw [heq] at hte
    rcases (by simpa using hte : t = v ∨ t = w) with rfl | rfl
    · exact hv ht
    · exact hw ht

lemma eraseVertices_dependsOn (U : Set V) :
    DependsOn (fun ω : Set E => G.eraseVertices ω U) (G.incidentEdges U)ᶜ := by
  intro ω ω' hω
  ext e
  change (ω e ∧ e ∉ G.incidentEdges U) ↔ (ω' e ∧ e ∉ G.incidentEdges U)
  by_cases he : e ∈ G.incidentEdges U
  · simp [he]
  · rw [(hω e he).to_iff]

lemma clusterObject_eq_of_incident {S : Set V} {C : ClusterObject V E} {ω ω' : Set E}
    (hC : G.clusterObject ω S = C)
    (hω : ∀ e ∈ G.incidentEdges C.1, e ∈ ω ↔ e ∈ ω') :
    G.clusterObject ω' S = C := by
  have hr : roots (G.openGraph ω) S = C.1 := congrArg Prod.fst hC
  have hr' := G.roots_eq_of_incident hr hω
  apply Prod.ext hr'
  change ω' ∩ G.incidentEdges (roots (G.openGraph ω') S) = C.2
  have he : ω ∩ G.incidentEdges (roots (G.openGraph ω) S) = C.2 := congrArg Prod.snd hC
  rw [hr] at he
  rw [hr', ← he]
  ext e
  constructor
  · intro hh
    exact ⟨(hω e hh.2).mpr hh.1, hh.2⟩
  · intro hh
    exact ⟨(hω e hh.2).mp hh.1, hh.2⟩

lemma dependsOn_exact_clusterObject (S : Set V) (C : ClusterObject V E) :
    DependsOn (fun ω : Set E => G.clusterObject ω S = C) (G.incidentEdges C.1) := by
  intro ω ω' hω
  apply propext
  constructor
  · exact fun h => G.clusterObject_eq_of_incident h (fun e he => (hω e he).to_iff)
  · exact fun h => G.clusterObject_eq_of_incident h (fun e he => (hω e he).symm.to_iff)

lemma roots_disjoint_symm (ω : Set E) (A B : Set V) :
    Disjoint (roots (G.openGraph ω) A) B ↔ Disjoint (roots (G.openGraph ω) B) A := by
  simp only [Set.disjoint_left]
  constructor
  · rintro h a ⟨b, hb, hba⟩ ha
    exact h ⟨a, ha, hba.symm⟩ hb
  · rintro h b ⟨a, ha, hab⟩ hb
    exact h ⟨b, hb, hab.symm⟩ ha

lemma roots_disjoint_roots (ω : Set E) {A B : Set V}
    (h : Disjoint (roots (G.openGraph ω) A) B) :
    Disjoint (roots (G.openGraph ω) A) (roots (G.openGraph ω) B) := by
  rw [Set.disjoint_left] at h ⊢
  rintro v ⟨a, ha, hav⟩ ⟨b, hb, hbv⟩
  exact h ⟨a, ha, hav.trans hbv.symm⟩ hb

lemma roots_erase_roots (ω : Set E) {A B : Set V}
    (h : Disjoint (roots (G.openGraph ω) A) B) :
    roots (G.openGraph (G.eraseVertices ω (roots (G.openGraph ω) A))) B =
      roots (G.openGraph ω) B := by
  rw [G.openGraph_eraseVertices]
  ext v
  constructor
  · exact fun hv => roots_mono (delete_le _ _) _ hv
  · rintro ⟨b, hb, hbv⟩
    refine ⟨b, hb, ?_⟩
    change v ∈ component (delete (G.openGraph ω) (roots (G.openGraph ω) A)) b
    rw [delete_roots_component _ _ _ (fun hh => Set.disjoint_left.mp h hh hb)]
    exact hbv

lemma openBond_roots {ω : Set E} {S : Set V} {e : E} (he : e ∈ ω)
    {v w : V} (hv : v ∈ G.ends e) (hw : w ∈ G.ends e)
    (hr : v ∈ roots (G.openGraph ω) S) : w ∈ roots (G.openGraph ω) S := by
  by_cases hvw : v = w
  · simpa [← hvw] using hr
  · have heq : G.ends e = s(v,w) := Sym2.eq_of_ne_mem hvw hv hw (by simp) (by simp)
    exact roots_closed hr ((SimpleGraph.fromEdgeSet_adj _).mpr
      ⟨⟨e, he, heq⟩, hvw⟩)

lemma clusterObject_erase_other (ω : Set E) {A B : Set V}
    (h : Disjoint (G.clusterObject ω A).1 B) :
    G.clusterObject (G.eraseVertices ω (G.clusterObject ω A).1) B = G.clusterObject ω B := by
  have hr := G.roots_erase_roots ω h
  apply Prod.ext hr
  change G.eraseVertices ω (roots (G.openGraph ω) A) ∩
    G.incidentEdges (roots (G.openGraph (G.eraseVertices ω (roots (G.openGraph ω) A))) B) =
    ω ∩ G.incidentEdges (roots (G.openGraph ω) B)
  rw [hr]
  ext e
  constructor
  · exact fun hh => ⟨hh.1.1, hh.2⟩
  · rintro ⟨he, hi⟩
    refine ⟨⟨he, ?_⟩, hi⟩
    rintro ⟨a, ha, hae⟩
    obtain ⟨b, hb, hbe⟩ := hi
    exact Set.disjoint_left.mp (G.roots_disjoint_roots ω h) ha
      (G.openBond_roots he hbe hae hb)

lemma clusterObject_exposure [Fintype V] [Fintype E]
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (F : ClusterObject V E → Set E → ℝ) :
    expect w (fun ω => F (G.clusterObject ω S)
      (G.eraseVertices ω (G.clusterObject ω S).1)) =
    expect w (fun ω => expect w (fun ω' => F (G.clusterObject ω S)
      (G.eraseVertices ω' (G.clusterObject ω S).1))) := by
  classical
  exact expect_exposure w hw (fun ω => G.clusterObject ω S)
    (fun C => G.incidentEdges C.1) (G.dependsOn_exact_clusterObject S)
    (fun C ω => F C (G.eraseVertices ω C.1))
    (fun C _ _ hω => congrArg (F C) (G.eraseVertices_dependsOn C.1 hω))

lemma clusterObject_avoidance_exposure [Fintype V] [Fintype E]
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (A B : Set V) (F : ClusterObject V E → ClusterObject V E → ℝ) :
    expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then
      F (G.clusterObject ω A) (G.clusterObject ω B) else 0) =
    expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then
      expect w (fun ω' => F (G.clusterObject ω A)
        (G.clusterObject (G.eraseVertices ω' (G.clusterObject ω A).1) B)) else 0) := by
  classical
  have he := G.clusterObject_exposure w hw A
    (fun C ω => if Disjoint C.1 B then F C (G.clusterObject ω B) else 0)
  have hl : (fun ω : E → Prop => if Disjoint (G.clusterObject ω A).1 B then
      F (G.clusterObject ω A)
        (G.clusterObject (G.eraseVertices ω (G.clusterObject ω A).1) B) else 0) =
      (fun ω => if Disjoint (G.clusterObject ω A).1 B then
        F (G.clusterObject ω A) (G.clusterObject ω B) else 0) := by
    funext ω
    split_ifs with h
    · rw [G.clusterObject_erase_other ω h]
    · rfl
  rw [hl] at he
  refine he.trans ?_
  congr 1
  funext ω
  split_ifs <;> simp [expect_zero]

end CriticalPercolation.BondGraph

end
end

end OAI
