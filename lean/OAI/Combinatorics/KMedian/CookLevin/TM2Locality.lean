import Mathlib
import OAI.Combinatorics.KMedian.Expanders.Stopped

namespace OAI

section Inline_PCPTM2Locality

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

def depth : Stmt Γ Λ σ → ℕ
  | .push _ _ q => depth q+1
  | .peek _ _ q => depth q+1
  | .pop _ _ q => depth q+1
  | .load _ q => depth q+1
  | .branch _ q r => max (depth q) (depth r)+1
  | .goto _ => 0
  | .halt => 0

def Safe (r : ℕ) (P T : ∀ k, List (Γ k)) : Prop :=
  ∀ k, r≤(P k).length ∨ T k=[]
def appendCfg (c : Cfg Γ Λ σ) (T : ∀ k, List (Γ k)) : Cfg Γ Λ σ :=
  ⟨c.l,c.var,fun k => c.stk k++T k⟩

lemma append_update (P T : ∀ k, List (Γ k)) (k : K) (L : List (Γ k)) :
    update (fun j => P j++T j) k (L++T k) = fun j => update P k L j++T j := by
  funext j
  by_cases h : j=k
  · subst j; simp
  · simp [h]
omit [DecidableEq K] in
lemma safe_mono {r s : ℕ} {P T : ∀ k, List (Γ k)} (h : Safe r P T) (hs : s≤r) :
    Safe s P T := fun k => (h k).imp_left (hs.trans ·)
lemma safe_update {r : ℕ} {P T : ∀ k, List (Γ k)} (h : Safe r P T)
    (k : K) (L : List (Γ k)) (hL : r≤L.length ∨ T k=[]) : Safe r (update P k L) T := by
  intro j
  by_cases he : j=k
  · subst j; simpa using hL
  · simpa [he] using h j
omit [DecidableEq K] in
lemma head_append {Element : Type*} {P T : List Element} (h : 1≤P.length ∨ T=[]) :
    (P++T).head?=P.head? := by
  rcases h with h|rfl
  · cases P <;> simp_all
  · simp
omit [DecidableEq K] in
lemma tail_append {Element : Type*} {P T : List Element} (h : 1≤P.length ∨ T=[]) :
    (P++T).tail=P.tail++T := by
  rcases h with h|rfl
  · cases P <;> simp_all
  · simp

lemma stepAux_suffix (q : Stmt Γ Λ σ) (v : σ) (P T : ∀ k, List (Γ k))
    (h : Safe (depth q) P T) :
    stepAux q v (fun k => P k++T k)=appendCfg (stepAux q v P) T := by
  induction q generalizing v P with
  | push k f q ih =>
    simp only [stepAux]
    rw [show f v::(P k++T k)=(f v::P k)++T k from rfl,append_update]
    apply ih
    apply safe_update (safe_mono h (by simp [depth]))
    exact (h k).imp_left (by simp only [depth,List.length_cons]; omega)
  | peek k f q ih =>
    simp only [stepAux]
    rw [head_append ((h k).imp_left (by simp only [depth]; omega))]
    exact ih _ _ (safe_mono h (by simp [depth]))
  | pop k f q ih =>
    simp only [stepAux]
    have hk : 1≤(P k).length ∨ T k=[] := (h k).imp_left (by simp only [depth]; omega)
    rw [head_append hk,tail_append hk,append_update]
    apply ih
    apply safe_update (safe_mono h (by simp [depth]))
    exact (h k).imp_left (by simp only [depth,List.length_tail]; omega)
  | load f q ih =>
    simp only [stepAux]
    exact ih _ _ (safe_mono h (by simp [depth]))
  | branch f q r ihq ihr =>
    simp only [stepAux]
    cases hf : f v
    · simp only [Bool.cond_false]
      exact ihr _ _ (safe_mono h (by simp [depth]; omega))
    · simp only [Bool.cond_true]
      exact ihq _ _ (safe_mono h (by simp [depth]; omega))
  | goto f => rfl
  | halt => rfl

omit [DecidableEq K] in
lemma take_drop_safe (r : ℕ) (S : ∀ k, List (Γ k)) :
    Safe r (fun k => (S k).take r) (fun k => (S k).drop r) := by
  intro k
  by_cases h : r≤(S k).length
  · exact Or.inl (by simp [List.length_take, min_eq_left h])
  · exact Or.inr (List.drop_eq_nil_of_le (by omega))
lemma stepAux_prefix (q : Stmt Γ Λ σ) (r : ℕ) (hq : depth q≤r)
    (v : σ) (S : ∀ k, List (Γ k)) :
    stepAux q v S=appendCfg (stepAux q v (fun k => (S k).take r))
      (fun k => (S k).drop r) := by
  have h := stepAux_suffix q v (fun k => (S k).take r) (fun k => (S k).drop r)
    (safe_mono (take_drop_safe r S) hq)
  simpa only [List.take_append_drop] using h

lemma stepAux_length (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (j : K) :
    ((stepAux q v S).stk j).length ≤ (S j).length+depth q := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [stepAux,depth]
    have h := ih v (update S k (f v::S k))
    by_cases he : j=k
    · subst j; simp only [update_self,List.length_cons] at h; omega
    · simp only [update_of_ne he] at h
      omega
  | peek k f q ih =>
    simp only [stepAux,depth]
    exact (ih _ _).trans (by omega)
  | pop k f q ih =>
    simp only [stepAux,depth]
    have h := ih (f v (S k).head?) (update S k (S k).tail)
    by_cases he : j=k
    · subst j; simp only [update_self,List.length_tail] at h; omega
    · simp only [update_of_ne he] at h
      omega
  | load f q ih =>
    simp only [stepAux,depth]
    exact (ih _ _).trans (by omega)
  | branch f q r ihq ihr =>
    simp only [stepAux,depth]
    cases hf : f v
    · simp only [Bool.cond_false]
      exact (ihr _ _).trans (by omega)
    · simp only [Bool.cond_true]
      exact (ihq _ _).trans (by omega)
  | goto f => simp [stepAux,depth]
  | halt => simp [stepAux,depth]
end MetricKMedian.PCP.Tableau

end Inline_PCPTM2Locality

end OAI
