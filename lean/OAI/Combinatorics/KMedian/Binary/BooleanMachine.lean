import Mathlib

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Turing StateTransition Function Finset

structure Machine where
  K : Type
  [decK : DecidableEq K]
  [finK : Fintype K]
  input : K
  output : K
  Label : Type
  [finLabel : Fintype Label]
  main : Label
  State : Type
  [finState : Fintype State]
  initial : State
  code : Label → TM2.Stmt (fun _ : K => Bool) Label State

attribute [instance] Machine.decK Machine.finK Machine.finLabel Machine.finState

namespace Machine

def tm (M : Machine) : FinTM2 where
  K := M.K
  k₀ := M.input
  k₁ := M.output
  Γ _ := Bool
  Λ := M.Label
  main := M.main
  σ := M.State
  initialState := M.initial
  m := M.code

instance allWorkFinite (M : Machine) (k : M.tm.K) : Fintype (M.tm.Γ k) :=
  inferInstanceAs (Fintype Bool)

abbrev Cfg (M : Machine) := TM2.Cfg (fun _ : M.K => Bool) M.Label M.State

def initialCfg (M : Machine) (s : List Bool) : M.Cfg :=
  ⟨some M.main, M.initial, fun k => if k=M.input then s else []⟩

def finalCfg (M : Machine) (s : List Bool) : M.Cfg :=
  ⟨none, M.initial, fun k => if k=M.output then s else []⟩

@[simp] theorem init_eq (M : Machine) (s : List Bool) :
    initList M.tm s=M.initialCfg s := by
  rfl

@[simp] theorem halt_eq (M : Machine) (s : List Bool) :
    haltList M.tm s=M.finalCfg s := by
  rfl

abbrev step (M : Machine) : M.Cfg → Option M.Cfg := TM2.step M.code

end Machine

theorem cfg_ext {K L S : Type} {a b : TM2.Cfg (fun _ : K => Bool) L S}
    (hl : a.l=b.l) (hv : a.var=b.var) (hs : a.stk=b.stk) : a=b := by
  cases a
  cases b
  cases hl
  cases hv
  cases hs
  rfl

inductive Trace {α : Type*} (f : α → Option α) : ℕ → α → α → Prop
  | refl (a : α) : Trace f 0 a a
  | cons {n : ℕ} {a b c : α} : f a=some b → Trace f n b c → Trace f (n+1) a c

namespace Trace
variable {α β : Type*} {f : α → Option α}

theorem trans {n m : ℕ} {a b c : α} (h : Trace f n a b) (g : Trace f m b c) :
    Trace f (n+m) a c := by
  induction h with
  | refl => simpa using g
  | cons hs ht ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cons hs (ih g)

theorem map {g : β → Option β} (e : α → β)
    (he : ∀ a b, f a=some b → g (e a)=some (e b))
    {n : ℕ} {a b : α} (h : Trace f n a b) : Trace g n (e a) (e b) := by
  induction h with
  | refl => exact refl _
  | cons hs _ ih => exact cons (he _ _ hs) ih

theorem iterate_eq {n : ℕ} {a b : α} (h : Trace f n a b) :
    (flip bind f)^[n] (some a)=some b := by
  induction h with
  | refl => rfl
  | cons hs ht ih =>
      rw [Function.iterate_succ_apply,show (flip bind f) (some _)=_ from hs]
      exact ih

theorem of_iterate {n : ℕ} {a b : α}
    (h : (flip bind f)^[n] (some a)=some b) : Trace f n a b := by
  induction n generalizing a with
  | zero =>
      have hab : a=b := Option.some.inj h
      subst b
      exact refl a
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h
      cases hc : f a with
      | none =>
          have hz : ∀ t : ℕ, (flip bind f)^[t] (none : Option α)=none := by
            intro t
            induction t with
            | zero => rfl
            | succ t iht =>
                rw [Function.iterate_succ_apply]
                exact iht
          change (flip bind f)^[n] (f a)=some b at h
          rw [hc,hz] at h
          contradiction
      | some c =>
          have hh : (flip bind f)^[n] (some c)=some b := by
            change (flip bind f)^[n] (f a)=some b at h
            rwa [hc] at h
          exact cons hc (ih hh)

def inTime {n : ℕ} {a b : α} (h : Trace f n a b) :
    EvalsToInTime f a (some b) n := ⟨⟨n,h.iterate_eq⟩,le_rfl⟩

theorem of_inTime {n : ℕ} {a b : α} (h : EvalsToInTime f a (some b) n) :
    Trace f h.steps a b := of_iterate h.evals_in_steps

end Trace

namespace Machine
variable {K L S : Type} [DecidableEq K]

def pushes : TM2.Stmt (fun _ : K => Bool) L S → ℕ
  | .push _ _ q => 1+pushes q
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

def volume [Fintype K] (s : K → List Bool) : ℕ := ∑ k, (s k).length

variable [Fintype K]

theorem volume_update (s : K → List Bool) (k : K) (v : List Bool) :
    volume (update s k v)+(s k).length=volume s+v.length := by
  classical
  unfold volume
  have he : (fun j => (update s k v j).length)=update (fun j => (s j).length) k v.length := by
    funext j
    simp only [update_apply]
    split <;> rfl
  rw [he,Finset.sum_update_of_mem (mem_univ k)]
  have hh := Finset.sum_erase_add (univ : Finset K) (fun j => (s j).length) (mem_univ k)
  simp only [Finset.sdiff_singleton_eq_erase]
  omega

theorem stepAux_volume (q : TM2.Stmt (fun _ : K => Bool) L S)
    (v : S) (s : K → List Bool) :
    volume (TM2.stepAux q v s).stk ≤ volume s+pushes q := by
  induction q generalizing v s with
  | push k g q ih =>
      have h := ih v (update s k (g v::s k))
      have hv := volume_update s k (g v::s k)
      simp only [List.length_cons] at hv
      simpa only [TM2.stepAux,pushes,Nat.add_assoc] using (by omega :
        volume (TM2.stepAux q v (update s k (g v::s k))).stk≤volume s+(1+pushes q))
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
      have h := ih (g v (s k).head?) (update s k (s k).tail)
      have hv := volume_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      simp only [TM2.stepAux,pushes]
      omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simpa only [TM2.stepAux,hg,Bool.false_eq_true,Bool.cond_false,pushes] using
          (ihr v s).trans (Nat.add_le_add_left (le_max_right (pushes q) _) _)
      · simpa only [TM2.stepAux,hg,Bool.cond_true,pushes] using
          (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (pushes r)) _)
  | goto g => simp only [TM2.stepAux,pushes,Nat.add_zero,le_refl]
  | halt => simp only [TM2.stepAux,pushes,Nat.add_zero,le_refl]

def growth (M : Machine) : ℕ := ∑ l, pushes (M.code l)

theorem step_volume (M : Machine) (a b : M.Cfg) (h : M.step a=some b) :
    volume b.stk ≤ volume a.stk+M.growth := by
  rcases a with ⟨l,v,s⟩
  cases l with
  | none => cases h
  | some l =>
      have hb : b=TM2.stepAux (M.code l) v s := (Option.some.inj h).symm
      rw [hb]
      exact (stepAux_volume _ _ _).trans (Nat.add_le_add_left
        (show pushes (M.code l) ≤ M.growth from
          single_le_sum (f:=fun x => pushes (M.code x)) (fun _ _ => Nat.zero_le _) (mem_univ l)) _)

theorem trace_volume (M : Machine) {n : ℕ} {a b : M.Cfg}
    (h : Trace M.step n a b) : volume b.stk ≤ volume a.stk+n*M.growth := by
  induction h with
  | refl => simp
  | @cons n a b c hab hbc ih =>
      have hs := M.step_volume a b hab
      calc
        _ ≤ volume b.stk+n*M.growth := ih
        _ ≤ volume a.stk+(n+1)*M.growth := by rw [Nat.add_mul]; omega

@[simp] theorem initial_volume (M : Machine) (s : List Bool) :
    volume (M.initialCfg s).stk=s.length := by
  classical
  simp only [initialCfg,volume,apply_ite List.length,List.length_nil]
  simp

@[simp] theorem final_volume (M : Machine) (s : List Bool) :
    volume (M.finalCfg s).stk=s.length := by
  classical
  simp only [finalCfg,volume,apply_ite List.length,List.length_nil]
  simp

theorem output_length (M : Machine) {s t : List Bool} {n : ℕ}
    (h : TM2OutputsInTime M.tm s (some t) n) : t.length ≤ s.length+n*M.growth := by
  have ht : Trace M.step h.steps (M.initialCfg s) (M.finalCfg t) :=
    Trace.of_iterate h.evals_in_steps
  have hv := M.trace_volume ht
  simp only [initial_volume,final_volume] at hv
  exact hv.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

end Machine
end MetricKMedian.Binary
end

end OAI
