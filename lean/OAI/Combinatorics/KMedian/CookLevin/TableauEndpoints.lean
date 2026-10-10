import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.TableauBoundary
import OAI.Combinatorics.KMedian.CookLevin.TableauCorrect
import OAI.Combinatorics.KMedian.CookLevin.TableauRun

namespace OAI

section Inline_PCPTableauEndpoints

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function Finset
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)
variable (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (T L : ℕ)
lemma bounded_sound (a : Var (K := K) T L → Value M)
    (ha : (boundedSystem M B T L).Satisfies a) (hL : ∀ k, (B.last.stk k).length≤L) :
    ∃ c : Cfg Γ Λ σ, (c.l,c.var)=B.firstControl ∧
      (∀ k, ∃ w, w.length≤B.certificateBound k ∧ c.stk k=B.firstPrefix k++w) ∧
      (advance M)^[T] c=B.last := by
  obtain ⟨ha,hb⟩ := (bounded_satisfies_iff M B T L a).mp ha
  obtain ⟨hc,hw,he⟩ := decoded_boundary M B T L a ha hb hL
  refine ⟨decodeCfg M T L a ha (time0 T),hc,hw,?_⟩
  exact (decoded_run M T L a ha).symm.trans he

variable [Inhabited σ]
lemma bounded_complete (cs : Fin (T+1) → Cfg Γ Λ σ)
    (hL : ∀ t k, ((cs t).stk k).length≤L)
    (hs : ∀ t : Fin T, cs (later T t)=advance M (cs (now T t)))
    (hc : ((cs (time0 T)).l,(cs (time0 T)).var)=B.firstControl)
    (hw : ∀ k, ∃ w, w.length≤B.certificateBound k ∧ (cs (time0 T)).stk k=B.firstPrefix k++w)
    (he : cs (timeLast T)=B.last) :
    (boundedSystem M B T L).Satisfies (honest M T L cs) := by
  apply (bounded_satisfies_iff M B T L _).mpr
  refine ⟨honest_satisfies M T L cs hL hs,?_⟩
  rintro ⟨side,cl⟩
  cases cl with
  | inl u =>
    cases side
    · exact hc
    · change ((cs (timeLast T)).l,(cs (timeLast T)).var)=(B.last.l,B.last.var)
      rw [he]
  | inr ki =>
    obtain ⟨k,i⟩ := ki
    cases side
    · change prefixCell (B.firstPrefix k) (B.certificateBound k) i.val ((cs (time0 T)).stk k)[i.val]?
      obtain ⟨w,hw,hs⟩ := hw k
      rw [hs]
      exact prefixCell_complete _ _ _ hw _
    · change ((cs (timeLast T)).stk k)[i.val]?=(B.last.stk k)[i.val]?
      rw [he]

lemma path_complete (c : Cfg Γ Λ σ)
    (hL : ∀ k, (c.stk k).length+radius M*T≤L)
    (hc : (c.l,c.var)=B.firstControl)
    (hw : ∀ k, ∃ w, w.length≤B.certificateBound k ∧ c.stk k=B.firstPrefix k++w)
    (he : (advance M)^[T] c=B.last) :
    ∃ a, (boundedSystem M B T L).Satisfies a := by
  let cs : Fin (T+1) → Cfg Γ Λ σ := fun t => (advance M)^[t.val] c
  refine ⟨honest M T L cs,bounded_complete M B T L cs ?_ ?_ hc hw he⟩
  · intro t k
    exact (run_length M c _ k).trans ((Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega : t.val≤T)) _).trans (hL k))
  · intro t
    exact Function.iterate_succ_apply' (advance M) t.val c
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauEndpoints

end OAI
