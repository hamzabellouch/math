import OAI.Combinatorics.ListHadwiger.RecursiveInduction

namespace OAI

namespace LinearListHadwiger.Recursion
open Finset Stage SmallList SimpleGraph
attribute [local instance] Classical.propDecidable

theorem final_bound_or_obstruction : ∃ C : ℕ, 1≤C ∧
    ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
      listChromaticNumber G≤C*hadwigerNumber G ∨
        FractionalObstruction G := by
  obtain ⟨K,Q,hK,hQ,hs⟩ := recursive_woven_or_obstruction
  refine ⟨2*(Q+6*K),by omega,?_⟩
  intro V _ _ G
  classical
  by_cases hb : FractionalObstruction G
  · exact Or.inr hb
  left
  have hminorfree (t : ℕ) (ht : 2≤t) (hm : hadwigerNumber G<t) :
      listChromaticNumber G≤(Q+6*K)*t := by
    by_contra hnot
    have hl : (Q+6*K)*t<listChromaticNumber G := by omega
    have hk : 1≤K*t := by nlinarith
    obtain ⟨P,hPc,hPl⟩ := list_connectivity_extraction G hk (by nlinarith)
    have hlist : Q*t≤listChromaticNumber (G.induce (↑P:Set V)) := by
      change listChromaticNumber G-6*(K*t)≤ell G P at hPl
      change Q*t≤ell G P
      have he : (Q+6*K)*t=Q*t+6*(K*t) := by ring
      rw [he] at hl
      omega
    rcases hs t (by omega) (↑P:Set V) (G.induce (↑P:Set V))
      (connected_induce_univ G P hPc) hlist with hw|hbad
    swap
    · exact hb (obstruction_induce G P hbad)
    obtain ⟨r,hr,hrP⟩ := choose_vertices (show t≤P.card by have hh:=hPc.1; nlinarith)
    have h0 (i : Fin 0) : V := Fin.elim0 i
    obtain ⟨A⟩ := woven_induce G P hw r hr hrP 0 (by omega) h0 h0
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    have hm' : HasCliqueMinor G t := ⟨A.model.branch,A.model.connected,A.model.disjoint,A.model.adjacent⟩
    exact (not_lt_of_ge (cliqueMinor_le_hadwigerNumber hm')) hm
  have hpos := one_le_hadwigerNumber G
  have hfinal := hminorfree (hadwigerNumber G+1) (by omega) (by omega)
  nlinarith

end LinearListHadwiger.Recursion

end OAI
