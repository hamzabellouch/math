import OAI.Combinatorics.MatchingEntropy.EdgeReduction

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds

theorem separable_lower_aux (n : ℕ) :
    ∀ {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessGraph V E), Fintype.card V=n → Even n →
      ∀ x ∈ G.polytope, separableLower x ≤ maxMatchingEntropy G x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E _ _ _ _ G hcard heven y hy
    by_cases hn : n=0
    · have : IsEmpty V := Fintype.card_eq_zero_iff.mp (hcard.trans hn)
      have : IsEmpty E := ⟨fun e => isEmptyElim (G.left e)⟩
      simpa [separableLower,entropy] using maxMatchingEntropy_nonneg G hy
    · have heven' : Even (Fintype.card V) := hcard ▸ heven
      have hPM : Nonempty G.Matching := by
        obtain ⟨p,hp⟩ := (G.mem_polytope_iff y).mp hy
        by_contra h
        have : IsEmpty G.Matching := not_nonempty_iff.mp h
        simpa using hp.1.2
      obtain ⟨x,hx,hmax⟩ := separableDefect_attains_max G heven' hPM
      obtain ⟨e₀,he₀⟩ := separable_max_has_forced G heven' (by omega) hx hmax
      have hc := G.remaining_vertex_card e₀
      have hlt : Fintype.card {v // G.RemainingVertex e₀ v}<n := by omega
      have hev : Even (Fintype.card {v // G.RemainingVertex e₀ v}) := by
        obtain ⟨r,hr⟩ := heven
        refine ⟨r-1,?_⟩
        omega
      obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
      have hs := G.forcedLaw_feasible hp e₀ he₀
      have hxr := ((G.deleteEndpoints e₀).mem_polytope_iff _).mpr ⟨_,hs⟩
      have hsmall := ih _ hlt (G.deleteEndpoints e₀) rfl hev _ hxr
      rw [G.separableLower_forced hx e₀ he₀] at hsmall
      have hxbound := hsmall.trans (G.maxMatchingEntropy_forced_le hx e₀ he₀)
      have hcompare := hmax y hy
      linarith

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem separable_lower (G : LooplessGraph V E) (hPM : Nonempty G.Matching)
    (x : E → ℝ) (hx : x ∈ G.polytope) : separableLower x ≤ maxMatchingEntropy G x := by
  obtain ⟨M⟩ := hPM
  have hev : Even (Fintype.card V) := ⟨M.val.card, by have hh := G.matching_card_twice M; omega⟩
  exact separable_lower_aux (Fintype.card V) G rfl hev x hx

end MatchingEntropyBounds

end

end OAI
