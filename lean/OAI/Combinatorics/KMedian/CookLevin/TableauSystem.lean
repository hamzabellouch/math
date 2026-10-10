import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.FiniteConstraints
import OAI.Combinatorics.KMedian.CookLevin.TableauLocal

namespace OAI

section Inline_PCPTableauSystem

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function Finset
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)
abbrev Value := Control (Λ := Λ) (σ := σ) × Response M × (∀ k, Option (Γ k))
abbrev Query := Unit ⊕ Unit ⊕ (K × Fin (radius M)) ⊕ Fin (2*radius M+1)
def q0 : Query M := .inl ()
def q1 : Query M := .inr (.inl ())
def qtop (k : K) (i : Fin (radius M)) : Query M := .inr (.inr (.inl (k,i)))
def qwin (h : Fin (2*radius M+1)) : Query M := .inr (.inr (.inr h))
instance queryNonempty : Nonempty (Query M) := ⟨q0 M⟩
abbrev Var (T L : ℕ) := Fin (T+1) ⊕ Fin T ⊕ (Fin (T+1) × K × Fin (L+1))
def ctrl (T L : ℕ) (t : Fin (T+1)) : Var (K := K) T L := .inl t
def resp (T L : ℕ) (t : Fin T) : Var (K := K) T L := .inr (.inl t)
def cell (T L : ℕ) (t : Fin (T+1)) (k : K) (i : Fin (L+1)) : Var (K := K) T L :=
  .inr (.inr (t,k,i))
def time0 (T : ℕ) : Fin (T+1) := ⟨0,by omega⟩
def now (T : ℕ) (t : Fin T) : Fin (T+1) := ⟨t.val,by omega⟩
def later (T : ℕ) (t : Fin T) : Fin (T+1) := ⟨t.val+1,by omega⟩
def clamp (L i : ℕ) : Fin (L+1) := ⟨min i L,by omega⟩

inductive Clause (T L : ℕ)
  | shape : Fin (T+1) → K → Fin L → Clause T L
  | end : Fin (T+1) → K → Clause T L
  | prefix : Fin T → Clause T L
  | control : Fin T → Clause T L
  | update : Fin T → K → Fin (L+1) → Clause T L
  deriving DecidableEq, Fintype

noncomputable def query (T L : ℕ) (test : Clause (K := K) T L) : Query M → Var (K := K) T L :=
  fun q => match test,q with
  | .shape t k i,.inl _ => cell T L t k ⟨i.val,by omega⟩
  | .shape t k i,_ => cell T L t k ⟨i.val+1,by omega⟩
  | .end t k,_ => cell T L t k ⟨L,by omega⟩
  | .prefix t,.inl _ => ctrl T L (now T t)
  | .prefix t,.inr (.inl _) => resp T L t
  | .prefix t,.inr (.inr (.inl (k,i))) => cell T L (now T t) k (clamp L i.val)
  | .prefix t,_ => ctrl T L (now T t)
  | .control t,.inl _ => ctrl T L (later T t)
  | .control t,_ => resp T L t
  | .update t k i,.inl _ => resp T L t
  | .update t k i,.inr (.inl _) => cell T L (later T t) k i
  | .update t k i,.inr (.inr (.inr h)) => cell T L (now T t) k (clamp L (i.val+radius M-h.val))
  | .update t k i,_ => resp T L t

def relation (T L : ℕ) (test : Clause (K := K) T L) (z : Query M → Value M) : Prop :=
  match test with
  | .shape _ k _ => (z (q0 M)).2.2 k=none → (z (q1 M)).2.2 k=none
  | .end _ k => (z (q0 M)).2.2 k=none
  | .prefix _ => PrefixRelation M (z (q0 M)).1
      (fun k i => (z (qtop M k i)).2.2 k) (z (q1 M)).2.1
  | .control _ => (z (q0 M)).1=(z (q1 M)).2.1.1
  | .update _ k i => (z (q1 M)).2.2 k=cellTable M k (category M i.val) ((z (q0 M)).2.1.2 k)
      (fun h => (z (qwin M h)).2.2 k)
noncomputable def system (T L : ℕ) : FiniteCSP (Var (K := K) T L) (Clause (K := K) T L) (Query M) (Value M) where
  query := query M T L
  accept t := univ.filter (relation M T L t)
lemma satisfies_iff (T L : ℕ) (a : Var (K := K) T L → Value M) :
    (system M T L).Satisfies a ↔ ∀ t, relation M T L t (a ∘ query M T L t) := by
  simp only [FiniteCSP.Satisfies,system,mem_filter,mem_univ,true_and]

def getControl (T L : ℕ) (a : Var (K := K) T L → Value M) (t : Fin (T+1)) : Control (Λ := Λ) (σ := σ) :=
  (a (ctrl T L t)).1
def getResponse (T L : ℕ) (a : Var (K := K) T L → Value M) (t : Fin T) : Response M :=
  (a (resp T L t)).2.1
def getRow (T L : ℕ) (a : Var (K := K) T L → Value M) (t : Fin (T+1)) (k : K) : Row (Γ k) L :=
  fun i => (a (cell T L t k i)).2.2 k
lemma row_valid (T L : ℕ) (a : Var (K := K) T L → Value M) (ha : (system M T L).Satisfies a)
    (t : Fin (T+1)) (k : K) : ValidRow L (getRow M T L a t k) := by
  have h := (satisfies_iff M T L a).mp ha
  exact ⟨h (.end t k),fun i => h (.shape t k i)⟩

noncomputable def decodeRow (T L : ℕ) (a : Var (K := K) T L → Value M)
    (ha : (system M T L).Satisfies a) (t : Fin (T+1)) (k : K) : List (Γ k) :=
  (valid_row_list L (getRow M T L a t k) (row_valid M T L a ha t k)).choose
lemma decodeRow_length (T L : ℕ) (a : Var (K := K) T L → Value M)
    (ha : (system M T L).Satisfies a) (t : Fin (T+1)) (k : K) :
    (decodeRow M T L a ha t k).length≤L :=
  (valid_row_list L (getRow M T L a t k) (row_valid M T L a ha t k)).choose_spec.1
lemma decodeRow_cell (T L : ℕ) (a : Var (K := K) T L → Value M)
    (ha : (system M T L).Satisfies a) (t : Fin (T+1)) (k : K) (i : ℕ) :
    (decodeRow M T L a ha t k)[i]?=rowCell L (getRow M T L a t k) i :=
  (valid_row_list L (getRow M T L a t k) (row_valid M T L a ha t k)).choose_spec.2 i
noncomputable def decodeCfg (T L : ℕ) (a : Var (K := K) T L → Value M)
    (ha : (system M T L).Satisfies a) (t : Fin (T+1)) : Cfg Γ Λ σ :=
  ⟨(getControl M T L a t).1,(getControl M T L a t).2,decodeRow M T L a ha t⟩

lemma clamp_decode (T L : ℕ) (a : Var (K := K) T L → Value M)
    (ha : (system M T L).Satisfies a) (t : Fin (T+1)) (k : K) (i : ℕ) :
    (a (cell T L t k (clamp L i))).2.2 k=((decodeCfg M T L a ha t).stk k)[i]? := by
  change clampedCell L (getRow M T L a t k) i=(decodeRow M T L a ha t k)[i]?
  rw [clampedCell_eq L _ (row_valid M T L a ha t k),decodeRow_cell]

lemma decoded_transition (T L : ℕ) (a : Var (K := K) T L → Value M)
    (ha : (system M T L).Satisfies a) (t : Fin T) :
    decodeCfg M T L a ha (later T t)=advance M (decodeCfg M T L a ha (now T t)) := by
  have h := (satisfies_iff M T L a).mp ha
  apply local_transition_exact M L _ _ (decodeRow_length M T L a ha (later T t)) (getResponse M T L a t)
  · have hp := h (.prefix t)
    dsimp only [relation,Function.comp_def,query,q0,q1,qtop] at hp
    simp_rw [clamp_decode M T L a ha] at hp
    simpa only [decodeCfg,getControl,getResponse,Prod.mk.eta] using hp
  · exact h (.control t)
  · intro k i hi
    have hp := h (.update t k ⟨i,by omega⟩)
    dsimp only [relation,Function.comp_def,query,q0,q1,qwin] at hp
    change (decodeRow M T L a ha (later T t) k)[i]?=_
    rw [decodeRow_cell,rowCell,dite_eq_left hi]
    simp_rw [clamp_decode M T L a ha] at hp
    simpa only [getResponse,getRow] using hp
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauSystem

end OAI
