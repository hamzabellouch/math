import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma finite_seed_tree_of_rank {S : Set V} (hS : S.Finite) (o : V)
    (r : V → ℕ)
    (hparent : ∀ v∈S, v≠o → ∃ w∈S, G.fullGraph.Adj w v ∧ r w<r v) :
    ∃ F : Set E, F.Finite ∧ F⊆G.inducedEdges S ∧ F.ncard ≤ S.ncard ∧
      ∀ v∈S, (G.openGraph F).Reachable o v := by
  let U := S\{o}
  have hU : U.Finite := hS.sdiff
  let := hU.fintype
  have hh : ∀ v : U, ∃ (w : V) (e : E), w∈S ∧ G.ends e=s(w,v.val) ∧
      w≠v.val ∧ r w<r v.val := by
    intro v
    obtain ⟨w,hw,⟨⟨e,_,he⟩,hne⟩,hr⟩ := hparent v.val v.property.1 v.property.2
    exact ⟨w,e,hw,he,hne,hr⟩
  choose w e hw hend hne hr using hh
  let F : Set E := Set.range e
  have hF : F.Finite := Set.finite_range e
  refine ⟨F,hF,?_,?_,?_⟩
  · rintro b ⟨v,rfl⟩ z hz
    rw [hend v] at hz
    rcases Sym2.mem_iff.mp hz with rfl|rfl
    · exact hw v
    · exact v.property.1
  · calc
      F.ncard ≤ (Set.univ : Set U).ncard := by
        simpa only [F,Set.image_univ] using (Set.ncard_image_le (f := e) (Set.finite_univ : (Set.univ : Set U).Finite))
      _ = U.ncard := by simp
      _ ≤ S.ncard := Set.ncard_le_ncard Set.sdiff_subset hS
  · intro v hv
    generalize hn : r v=n
    induction n using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hvo : v=o
      · subst v; exact SimpleGraph.Reachable.refl _
      · let a : U := ⟨v,hv,hvo⟩
        have hprev := ih (r (w a)) (by simpa only [← hn] using hr a) (w a) (hw a) rfl
        apply hprev.trans
        exact (show (G.openGraph F).Adj (w a) v from
          ⟨⟨e a,⟨a,rfl⟩,hend a⟩,hne a⟩).reachable

def ballRank (o v : V) : ℕ :=
  if h : ∃ n, v∈G.vertexBall o n then Nat.find h else 0

lemma ballRank_mem {o v : V} (h : ∃ n, v∈G.vertexBall o n) :
    v∈G.vertexBall o (G.ballRank o v) := by
  simp only [ballRank,dite_eq_left h]
  exact Nat.find_spec h

lemma ballRank_le {o v : V} {n : ℕ} (h : v∈G.vertexBall o n) : G.ballRank o v ≤ n := by
  have he : ∃ k, v∈G.vertexBall o k := ⟨n,h⟩
  simp only [ballRank,dite_eq_left he]
  exact Nat.find_min' he h

lemma ballRank_eq_zero_iff {o v : V} (h : ∃ n, v∈G.vertexBall o n) :
    G.ballRank o v=0 ↔ v=o := by
  constructor
  · intro hz
    have hh := G.ballRank_mem h
    rw [hz] at hh
    exact hh
  · intro hvo
    subst v
    exact Nat.eq_zero_of_le_zero (G.ballRank_le (show o∈G.vertexBall o 0 from rfl))

lemma ballRank_predecessor {o v : V} (h : ∃ n, v∈G.vertexBall o n) (hne : v≠o) :
    ∃ w, G.fullGraph.Adj w v ∧ G.ballRank o w+1=G.ballRank o v ∧
      w∈G.vertexBall o (G.ballRank o w) := by
  have hn : 0 < G.ballRank o v := Nat.pos_of_ne_zero (fun hh => hne ((G.ballRank_eq_zero_iff h).mp hh))
  obtain ⟨n,heq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hv := G.ballRank_mem h
  rw [heq] at hv
  rcases hv with hv|hv
  · have hb := G.ballRank_le hv
    omega
  · obtain ⟨w,hw,hvw⟩ := Set.mem_iUnion₂.mp hv
    have h1 := G.ballRank_le hw
    have h2 := G.ballRank_le (G.vertexBall_step (G.ballRank_mem ⟨n,hw⟩) hvw)
    refine ⟨w,hvw,by omega,G.ballRank_mem ⟨n,hw⟩⟩

lemma finite_seed_tree (hlocal : G.LocallyFinite) (o : V) (m : ℕ) :
    ∃ F : Set E, F.Finite ∧ F⊆G.inducedEdges (G.vertexBall o m) ∧
      F.ncard ≤ (G.vertexBall o m).ncard ∧
      ∀ v∈G.vertexBall o m, (G.openGraph F).Reachable o v := by
  apply G.finite_seed_tree_of_rank (G.vertexBall_finite hlocal o m) o (G.ballRank o)
  intro v hv hne
  obtain ⟨w,hw,hr,hmem⟩ := G.ballRank_predecessor ⟨m,hv⟩ hne
  exact ⟨w,G.vertexBall_mono o (by have := G.ballRank_le hv; omega) hmem,hw,by omega⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
