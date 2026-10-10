import Mathlib
import OAI.Combinatorics.MatchingCount.Probability.Variance
import OAI.Combinatorics.MatchingCount.Graphs.AdaptiveStream

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q R : Type} [Inhabited Γ]

structure Cfg (Γ Q : Type) [Inhabited Γ] where
  state : Option Q
  tape : Tape Γ

abbrev Table (Γ Q : Type) := Q → Γ → Bool → Option (Q × TM0.Stmt Γ)

def tick (M : Table Γ Q) (c : Cfg Γ Q) (b : Bool) : Cfg Γ Q :=
  match c.state with
  | none => c
  | some q => match M q c.tape.head b with
    | none => ⟨none,c.tape⟩
    | some (q',a) => ⟨some q',match a with
      | .move d => c.tape.move d
      | .write s => c.tape.write s⟩

def execute (M : Table Γ Q) : ℕ → Cfg Γ Q → Stream → Cfg Γ Q
  | 0,c,_ => c
  | n+1,c,b => execute M n (tick M c (b 0)) (shift 1 b)

lemma execute_add (M : Table Γ Q) (n m : ℕ) (c : Cfg Γ Q) (b : Stream) :
    execute M (n+m) c b=execute M m (execute M n c b) (shift n b) := by
  induction n generalizing c b with
  | zero => simp only [execute,Nat.zero_add,shift_zero]
  | succ n ih =>
    rw [Nat.succ_add,execute,ih,execute]
    congr 1
    funext i
    simp only [shift]
    congr 1
    omega

lemma execute_halted (M : Table Γ Q) (n : ℕ) (T : Tape Γ) (b : Stream) :
    execute M n ⟨none,T⟩ b=⟨none,T⟩ := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => exact ih (shift 1 b)

def experiment (M : Table Γ Q) : ℕ → Cfg Γ Q → Experiment (Cfg Γ Q)
  | 0,c => .done c
  | n+1,c => .read (fun b=>experiment M n (tick M c b))

lemma experiment_cost (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) :
    (experiment M n c).cost=n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [experiment,Experiment.cost,ih,max_self]; omega

lemma experiment_run (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (b : Stream) :
    (experiment M n c).run b=(execute M n c b,n) := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih => simp only [experiment,Experiment.run,ih,execute]; congr 1; omega

theorem physical_law (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (f : Cfg Γ Q → ℚ) :
    average (fun b : Bits n=>f (execute M n c (extend b)))=(experiment M n c).mean f := by
  have h:=Experiment.average_run (experiment M n c) f n (by rw [experiment_cost])
  simpa only [experiment_run] using h

variable [Fintype Q] [Inhabited Q]

noncomputable def enumeration : Q ≃ Fin (Fintype.card Q-1+1) := by
  let e : Q ≃ Fin (Fintype.card Q-1+1) := Fintype.equivFinOfCardEq
    (Nat.sub_add_cancel Fintype.card_pos).symm
  exact e.trans (Equiv.swap (e default) 0)

@[simp] lemma enumeration_default : enumeration (Q:=Q) default=0 := by
  classical
  simp only [enumeration,Equiv.trans_apply,Equiv.swap_apply_left]

noncomputable def machine (M : Table Symbol Q) : RandomMachine where
  states := Fintype.card Q-1
  transition q a b := (M ((enumeration (Q:=Q)).symm q) a b).map
    (fun qa=>(enumeration qa.1,qa.2))

noncomputable def sealCfg (M : Table Symbol Q) (c : Cfg Symbol Q) : Configuration (machine M) :=
  ⟨c.state.map enumeration,c.tape⟩

lemma tick_seal (M : Table Symbol Q) (c : Cfg Symbol Q) (b : Bool) :
    MatchingFPRAS.tick (machine M) (sealCfg M c) b=sealCfg M (tick M c b) := by
  cases c with
  | mk s T => cases s with
    | none => rfl
    | some q =>
      simp only [MatchingFPRAS.tick,sealCfg,machine,Option.map_some,Equiv.symm_apply_apply,tick]
      cases h:M q T.head b with
      | none => rfl
      | some qa => rcases qa with ⟨q',a⟩; cases a <;> rfl

omit [Fintype Q] [Inhabited Q] in
lemma execute_list (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (b : Bits n) :
    execute M n c (extend b)=(List.ofFn b).foldl (tick M) c := by
  induction n generalizing c with
  | zero => simp [execute]
  | succ n ih =>
    rw [execute,List.ofFn_succ,List.foldl_cons]
    have h0 : extend b 0=b 0 := by simp [extend]
    rw [h0,←ih]
    have he : ∀ i, i<n → shift 1 (extend b) i=extend (fun j : Fin n=>b j.succ) i := by
      intro i hi
      simp only [shift,extend,dite_eq_left hi,dite_eq_left (by omega : 1+i<n+1)]
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    have hc : ∀ (k : ℕ) (a d : Stream), (∀ i,i<k→a i=d i) →
        ∀ c, execute M k c a=execute M k c d := by
      intro k
      induction k with
      | zero => intros; rfl
      | succ k hk =>
        intro a d had c
        simp only [execute,had 0 (by omega)]
        apply hk
        intro i hi
        exact had (1+i) (by omega)
    exact hc n _ _ he _

lemma foldl_seal (M : Table Symbol Q) (bs : List Bool) (c : Cfg Symbol Q) :
    bs.foldl (MatchingFPRAS.tick (machine M)) (sealCfg M c)=sealCfg M (bs.foldl (tick M) c) := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => rw [List.foldl_cons,tick_seal,ih,List.foldl_cons]

lemma initial_seal (M : Table Symbol Q) (input : List Symbol) :
    sealCfg M ⟨some default,Tape.mk₁ input⟩=MatchingFPRAS.initial (machine M) input := by
  change (⟨some (enumeration default),Tape.mk₁ input⟩ : Configuration (machine M))=⟨some 0,Tape.mk₁ input⟩
  rw [enumeration_default]
  rfl

theorem run_seal (M : Table Symbol Q) (input : List Symbol) (n : ℕ) (b : Bits n) :
    MatchingFPRAS.run (machine M) input b=
      sealCfg M (execute M n ⟨some default,Tape.mk₁ input⟩ (extend b)) := by
  unfold MatchingFPRAS.run
  rw [←initial_seal,foldl_seal,execute_list]

end MatchingFPRAS.PhysicalPost

end OAI
