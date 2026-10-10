import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.TableauSystem

namespace OAI

section Inline_PCPTableauCorrect

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function Finset
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)

lemma decoded_run (T L : ℕ) (a : Var (K := K) T L → Value M)
    (ha : (system M T L).Satisfies a) :
    decodeCfg M T L a ha ⟨T,by omega⟩ = (advance M)^[T] (decodeCfg M T L a ha (time0 T)) := by
  have hrun : ∀ n, ∀ hn : n≤T, decodeCfg M T L a ha ⟨n,by omega⟩ =
      (advance M)^[n] (decodeCfg M T L a ha (time0 T)) := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      have hh := decoded_transition M T L a ha ⟨n,by omega⟩
      change decodeCfg M T L a ha ⟨n+1,by omega⟩ =
        advance M (decodeCfg M T L a ha ⟨n,by omega⟩) at hh
      rw [hh,ih (by omega),Function.iterate_succ_apply']
  exact hrun T le_rfl

variable [Inhabited σ]
def emptyControl : Control (Λ := Λ) (σ := σ) := (none,default)
def emptyResponse : Response M := ⟨emptyControl,fun _ => ⟨[],by simp⟩⟩
noncomputable def honest (T L : ℕ) (cs : Fin (T+1) → Cfg Γ Λ σ) : Var (K := K) T L → Value M
  | .inl t => ⟨((cs t).l,(cs t).var),emptyResponse M,fun _ => none⟩
  | .inr (.inl t) => ⟨emptyControl,respond M ((cs (now T t)).l,(cs (now T t)).var)
      (stackPrefix M (cs (now T t)).stk),fun _ => none⟩
  | .inr (.inr (t,_,i)) => ⟨emptyControl,emptyResponse M,fun k => ((cs t).stk k)[i.val]?⟩
omit [Fintype K] [Fintype σ] [∀ k, Fintype (Γ k)] in
lemma honest_clamp (T L : ℕ) (cs : Fin (T+1) → Cfg Γ Λ σ) (hL : ∀ t k, ((cs t).stk k).length≤L)
    (t : Fin (T+1)) (k : K) (i : ℕ) :
    (honest M T L cs (cell T L t k (clamp L i))).2.2 k=((cs t).stk k)[i]? := by
  change ((cs t).stk k)[min i L]?=((cs t).stk k)[i]?
  by_cases hi : i≤L
  · rw [min_eq_left hi]
  · rw [min_eq_right (by omega : L ≤ i),List.getElem?_eq_none (hL t k),
      List.getElem?_eq_none ((hL t k).trans (by omega : L ≤ i))]

lemma honest_satisfies (T L : ℕ) (cs : Fin (T+1) → Cfg Γ Λ σ)
    (hL : ∀ t k, ((cs t).stk k).length≤L)
    (hs : ∀ t : Fin T, cs (later T t)=advance M (cs (now T t))) :
    (system M T L).Satisfies (honest M T L cs) := by
  apply (satisfies_iff M T L _).mpr
  intro cl
  cases cl with
  | shape t k i =>
    change ((cs t).stk k)[i.val]?=none → ((cs t).stk k)[i.val+1]?=none
    intro hi
    exact List.getElem?_eq_none (by have := List.getElem?_eq_none_iff.mp hi; omega)
  | «end» t k => exact List.getElem?_eq_none (hL t k)
  | «prefix» t =>
    dsimp only [relation,Function.comp_def,query,q0,q1,qtop]
    simp_rw [honest_clamp M T L cs hL]
    exact prefixRelation_complete M (cs (now T t))
  | control t =>
    change ((cs (later T t)).l,(cs (later T t)).var)=_
    rw [hs t]
    exact response_control M (cs (now T t))
  | update t k i =>
    dsimp only [relation,Function.comp_def,query,q0,q1,qwin]
    simp_rw [honest_clamp M T L cs hL]
    change ((cs (later T t)).stk k)[i.val]?=cellTable M k (category M i.val)
      ((respond M ((cs (now T t)).l,(cs (now T t)).var) (stackPrefix M (cs (now T t)).stk)).2 k)
      (fun h => ((cs (now T t)).stk k)[i.val+radius M-h.val]?)
    rw [hs t,cellTable_exact]
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauCorrect

end OAI
