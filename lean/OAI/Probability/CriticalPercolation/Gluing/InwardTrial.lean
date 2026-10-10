import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Criticality.FiniteSeedTree
import OAI.Probability.CriticalPercolation.Gluing.CollarDistance
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma inward_path (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    (v : V) (l : ℕ) (hl : l ≤ G.distanceTo B v) :
    ∃ (y : V) (P : Set E), P.Finite ∧ P.ncard ≤ l ∧
      G.distanceTo B y+l=G.distanceTo B v ∧ y∈G.vertexBall v l ∧
      P⊆G.inducedEdges (G.vertexBall v l∩{z | G.distanceTo B z ≤ G.distanceTo B v}) ∧
      P⊆(G.inducedEdges {z | G.distanceTo B v ≤ G.distanceTo B z})ᶜ ∧
      (G.openGraph P).Reachable v y := by
  induction l generalizing v with
  | zero =>
    exact ⟨v,∅,Set.finite_empty,by simp,by omega,rfl,Set.empty_subset _,Set.empty_subset _,
      SimpleGraph.Reachable.refl _⟩
  | succ l ih =>
    obtain ⟨w,hw,hr⟩ := G.distanceTo_predecessor hc hB v (by omega)
    obtain ⟨y,P,hP,hcard,hy,hyball,hends,hfresh,hreach⟩ := ih w (by omega)
    have hwball : w∈G.vertexBall v 1 := G.vertexBall_step (G.mem_vertexBall_self v 0) hw
    obtain ⟨⟨e,_,he⟩,hne⟩ := hw
    refine ⟨y,insert e P,hP.insert _,?_,by omega,?_,?_,?_,?_⟩
    · exact (Set.ncard_insert_le _ _).trans (by omega)
    · simpa only [Nat.add_comm 1] using G.vertexBall_add hwball l hyball
    · intro f hf z hz
      rcases hf with rfl|hf
      · rw [he] at hz
        have hz' : z=v ∨ z=w := Sym2.mem_iff.mp hz
        rcases hz' with hz'|hz'
        · subst z
          exact ⟨G.mem_vertexBall_self v (l+1),show G.distanceTo B v ≤ G.distanceTo B v from le_rfl⟩
        · subst z
          exact ⟨G.vertexBall_mono v (by omega) hwball,by change G.distanceTo B w ≤ G.distanceTo B v; omega⟩
      · have hh := hends hf z hz
        have hh2 : G.distanceTo B z ≤ G.distanceTo B w := hh.2
        refine ⟨?_,by change G.distanceTo B z ≤ G.distanceTo B v; omega⟩
        simpa only [Nat.add_comm 1] using G.vertexBall_add hwball l hh.1
    · intro f hf hf'
      rcases hf with rfl|hf
      · have hh := hf' w (by rw [he]; simp)
        change G.distanceTo B v ≤ G.distanceTo B w at hh
        omega
      · apply hfresh hf
        intro z hz
        have hh := hf' z hz
        change G.distanceTo B v ≤ G.distanceTo B z at hh
        change G.distanceTo B w ≤ G.distanceTo B z
        omega
    · apply (show (G.openGraph (insert e P)).Adj v w from
          ⟨⟨e,Set.mem_insert e P,he⟩,hne⟩).reachable.trans
      exact hreach.mono (G.openGraph_mono (Set.subset_insert e P))

lemma inward_seed_trial (hc : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    {B : Set V} (hB : B.Nonempty) (v : V) (m : ℕ) (hm : m<G.distanceTo B v) :
    ∃ (y : V) (F : Set E), F.Finite ∧
      F.ncard ≤ m+1+(G.vertexBall y m).ncard ∧
      G.distanceTo B y+(m+1)=G.distanceTo B v ∧
      F⊆G.inducedEdges (G.vertexBall v (2*m+1)∩{z | G.distanceTo B z ≤ G.distanceTo B v}) ∧
      F⊆(G.inducedEdges {z | G.distanceTo B v ≤ G.distanceTo B z})ᶜ ∧
      ∀ z∈G.vertexBall y m, (G.openGraph F).Reachable v z := by
  obtain ⟨y,P,hP,hcard,hy,hyball,hends,hfresh,hreach⟩ := G.inward_path hc hB v (m+1) (by omega)
  obtain ⟨Q,hQ,hQends,hQcard,hQreach⟩ := G.finite_seed_tree hlocal y m
  refine ⟨y,P∪Q,hP.union hQ,?_,hy,?_,?_,?_⟩
  · exact (Set.ncard_union_le P Q).trans (by omega)
  · intro e he z hz
    rcases he with he|he
    · have hh := hends he z hz
      exact ⟨G.vertexBall_mono v (by omega) hh.1,hh.2⟩
    · have hh := hQends he z hz
      have hle := G.distanceTo_ball hc hB hh
      refine ⟨?_,by change G.distanceTo B z ≤ G.distanceTo B v; omega⟩
      have := G.vertexBall_add hyball m hh
      simpa only [show m+1+m=2*m+1 by omega] using this
  · intro e he he'
    rcases he with he|he
    · exact hfresh he he'
    · obtain ⟨⟨x,z⟩,hxz⟩ := Sym2.mk_surjective (G.ends e)
      have hx : x∈G.ends e := by rw [← hxz]; simp
      have hh := G.distanceTo_ball hc hB (hQends he x hx)
      have hh' := he' x hx
      change G.distanceTo B v ≤ G.distanceTo B x at hh'
      omega
  · intro z hz
    exact (hreach.mono (G.openGraph_mono Set.subset_union_left)).trans
      ((hQreach z hz).mono (G.openGraph_mono Set.subset_union_right))

end CriticalPercolation.BondGraph
end
end
end

end OAI
