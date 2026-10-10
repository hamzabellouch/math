import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced
import OAI.Probability.CriticalPercolation.GraphGeometry.HitEvent
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def exteriorCluster (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) : Set V :=
  G.cluster (ω∩G.inducedEdges {v | j ≤ π v}) o

def levelContacts (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) : Set V :=
  G.exteriorCluster π j o ω∩{v | π v=j}

def contactDrop (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) : Set E :=
  {e | ∃ v∈G.levelContacts π j o ω, ∃ w, π w<j ∧ G.ends e=s(v,w)}

lemma contactDrop_subset_incident (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) :
    G.contactDrop π j o ω ⊆ G.incidentEdges (G.levelContacts π j o ω) := by
  rintro e ⟨v,hv,w,hw,he⟩
  exact ⟨v,hv,by rw [he]; simp⟩

lemma contactDrop_disjoint_exterior (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) :
    Disjoint (G.contactDrop π j o ω) (G.inducedEdges {v | j ≤ π v}) := by
  apply Set.disjoint_left.mpr
  rintro e ⟨v,hv,w,hw,he⟩ he'
  exact (not_le.mpr hw) (he' w (by rw [he]; simp))

lemma exteriorCluster_subset_level (π : V → ℤ) (j : ℤ) (o : V)
    (ho : j ≤ π o) (ω : Set E) : G.exteriorCluster π j o ω ⊆ {v | j ≤ π v} := by
  intro v hv
  have hc : ∀ ⦃x y⦄, x∈{v | j ≤ π v} →
      (G.openGraph (ω∩G.inducedEdges {v | j ≤ π v})).Adj x y → y∈{v | j ≤ π v} := by
    intro x y hx hxy
    obtain ⟨⟨e,he,hend⟩,_⟩ := hxy
    exact he.2 y (by rw [hend]; simp)
  exact ClusterDeletion.reachable_mem_of_closed hc ho hv

lemma cluster_eq_exterior_of_drop_closed (π : V → ℤ) (j : ℤ) (o : V)
    (ho : j ≤ π o)
    (hcross : ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (ω : Set E) (hclosed : Disjoint (G.contactDrop π j o ω) ω) :
    G.cluster ω o=G.exteriorCluster π j o ω := by
  apply Set.Subset.antisymm
  · intro v hv
    have hc : ∀ ⦃x y⦄, x∈G.exteriorCluster π j o ω →
        (G.openGraph ω).Adj x y → y∈G.exteriorCluster π j o ω := by
      intro x y hx hxy
      obtain ⟨⟨e,he,hend⟩,hne⟩ := hxy
      have hxj := G.exteriorCluster_subset_level π j o ho ω hx
      by_cases hy : j ≤ π y
      · apply hx.trans
        apply SimpleGraph.Adj.reachable
        refine ⟨⟨e,⟨he,?_⟩,hend⟩,hne⟩
        intro z hz
        rw [hend] at hz
        rcases Sym2.mem_iff.mp hz with rfl|rfl
        · exact hxj
        · exact hy
      · have hy' := lt_of_not_ge hy
        exact False.elim (Set.disjoint_left.mp hclosed
          ⟨x,⟨hx,hcross e x y hend hxj hy'⟩,y,hy',hend⟩ he)
    exact ClusterDeletion.reachable_mem_of_closed hc (SimpleGraph.Reachable.refl o) hv
  · exact G.cluster_mono Set.inter_subset_left o

def minimumLevel (π : V → ℤ) (o : V) (j : ℤ) : Set (Set E) :=
  G.hitEvent o {v | π v=j}\G.hitEvent o {v | π v<j}

lemma minimumLevel_of_drop_closed (π : V → ℤ) (j : ℤ) (o : V)
    (ho : j ≤ π o)
    (hcross : ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (ω : Set E) (hcontact : (G.levelContacts π j o ω).Nonempty)
    (hclosed : Disjoint (G.contactDrop π j o ω) ω) :
    ω∈G.minimumLevel π o j := by
  have he := G.cluster_eq_exterior_of_drop_closed π j o ho hcross ω hclosed
  constructor
  · obtain ⟨v,hv,hj⟩ := hcontact
    exact ⟨v,he.symm ▸ hv,hj⟩
  · rintro ⟨v,hv,hj⟩
    have hlt : π v < j := hj
    have hle : j ≤ π v := G.exteriorCluster_subset_level π j o ho ω (he ▸ hv)
    omega

lemma minimumLevel_pairwiseDisjoint (π : V → ℤ) (o : V) :
    Pairwise (fun i j => Disjoint (G.minimumLevel π o i) (G.minimumLevel π o j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro ω ⟨⟨v,hv,hvi⟩,hnoti⟩ ⟨⟨w,hw,hwj⟩,hnotj⟩
  rcases lt_or_gt_of_ne hij with hlt|hgt
  · exact hnotj ⟨v,hv,by change π v < j; rw [hvi]; exact hlt⟩
  · exact hnoti ⟨w,hw,by change π w < i; rw [hwj]; exact hgt⟩

lemma measurableSet_minimumLevel [Countable V] [Countable E] (π : V → ℤ) (o : V) (j : ℤ) :
    MeasurableSet (G.minimumLevel π o j) :=
  (G.measurableSet_hitEvent o _).diff (G.measurableSet_hitEvent o _)

end CriticalPercolation.BondGraph
end
end
end

end OAI
