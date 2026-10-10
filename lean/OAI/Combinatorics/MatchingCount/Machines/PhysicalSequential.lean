import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.PhysicalRestriction
import OAI.Combinatorics.MatchingCount.Machines.PhysicalProcess
import OAI.Combinatorics.MatchingCount.Graphs.ExperimentSupport

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q R α β : Type} [Inhabited Γ]

def seq (M : Table Γ Q) (N : Table Γ R) (r₀ : R) : Table Γ (Q⊕R)
  | .inl q,a,b => match M q a b with
    | none => some (.inr r₀,.write a)
    | some (q',act) => some (.inl q',act)
  | .inr r,a,b => (N r a b).map (fun ra=>(Sum.inr ra.1,ra.2))
def leftCfg (r₀ : R) (c : Cfg Γ Q) : Cfg Γ (Q⊕R) :=
  ⟨some (c.state.elim (Sum.inr r₀) Sum.inl),c.tape⟩
def rightCfg (c : Cfg Γ R) : Cfg Γ (Q⊕R) := ⟨c.state.map Sum.inr,c.tape⟩
lemma tick_left (M : Table Γ Q) (N : Table Γ R) (r₀ : R) (q : Q) (T : Tape Γ) (b : Bool) :
    tick (seq M N r₀) (leftCfg r₀ ⟨some q,T⟩) b=leftCfg r₀ (tick M ⟨some q,T⟩ b) := by
  cases h : M q T.head b with
  | none => simp only [tick,leftCfg,seq,h,Option.elim_some,Option.elim_none,Tape.write_self]
  | some qa => rcases qa with ⟨q',act⟩;cases act <;> simp only [tick,leftCfg,seq,h,Option.elim_some]
lemma tick_right (M : Table Γ Q) (N : Table Γ R) (r₀ : R) (c : Cfg Γ R) (b : Bool) :
    tick (seq M N r₀) (rightCfg c) b=rightCfg (tick N c b) := by
  rcases c with ⟨s,T⟩
  cases s with
  | none => rfl
  | some r =>
    cases h:N r T.head b with
    | none => simp only [tick,rightCfg,Option.map_some,seq,h,Option.map_none]
    | some ra => rcases ra with ⟨r',act⟩;cases act <;> simp only [tick,rightCfg,seq,h,Option.map_some]
lemma execute_right (M : Table Γ Q) (N : Table Γ R) (r₀ : R) (n : ℕ) (c : Cfg Γ R) (b : Stream) :
    execute (seq M N r₀) n (rightCfg c) b=rightCfg (execute N n c b) := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih => rw [execute,tick_right,ih,execute]
lemma Implements.right {M : Table Γ Q} {N : Table Γ R} (r₀ : R) {out : α→Cfg Γ R}
    {c : Cfg Γ R} {p : Experiment α} (h : Implements N out c p) :
    Implements (seq M N r₀) (rightCfg ∘ out) (rightCfg c) p := by
  induction h with
  | done a => exact .done a
  | read c f h ih => apply Implements.read;intro b;rw [tick_right];exact ih b
  | delay c d n p hs hr ih =>
    exact .delay _ _ n _ (fun b=>by rw [execute_right,hs]) ih

def early (M : Table Γ Q) : ℕ→Cfg Γ Q→Experiment (Cfg Γ Q)
  | 0,c => .done c
  | n+1,c => match c.state with
    | none => .done c
    | some _ => .read (fun b=>early M n (tick M c b))
lemma early_cost (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) : (early M n c).cost≤n := by
  induction n generalizing c with
  | zero => exact le_rfl
  | succ n ih =>
    cases h:c.state <;> simp only [early,h,Experiment.cost]
    · omega
    · have h0:=ih (tick M c false); have h1:=ih (tick M c true); omega
lemma early_run (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (b : Stream) :
    ((early M n c).run b).1=execute M n c b := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih =>
    rcases c with ⟨s,T⟩
    cases s with
    | none => rw [execute_halted];rfl
    | some q => simp only [early,Experiment.run,execute];exact ih _ _
lemma early_mean (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (f : Cfg Γ Q→ℚ) :
    (early M n c).mean f=average (fun b : Bits n=>f (execute M n c (extend b))) := by
  simpa only [early_run] using (Experiment.average_run (early M n c) f n (early_cost M n c)).symm
lemma early_left (M : Table Γ Q) (N : Table Γ R) (r₀ : R) (n : ℕ) (c : Cfg Γ Q) :
    Implements (seq M N r₀) (leftCfg r₀) (leftCfg r₀ c) (early M n c) := by
  induction n generalizing c with
  | zero => exact .done c
  | succ n ih =>
    rcases c with ⟨s,T⟩
    cases s with
    | none => exact .done _
    | some q =>
      apply Implements.read
      intro b
      rw [tick_left]
      exact ih _
lemma Implements.early_mean {M : Table Γ Q} {out : α→Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment α} (h : Implements M out c p) (halt : ∀ a,(out a).state=none)
    (n : ℕ) (hn : p.cost≤n) (f : Cfg Γ Q→ℚ) :
    (early M n c).mean f=p.mean (fun a=>f (out a)) := by
  rw [PhysicalPost.early_mean]
  exact h.fair_law halt n hn f
lemma Implements.bind_all {M : Table Γ Q} {out : α→Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment α} (h : Implements M out c p) (q : α→Experiment β) (out' : β→Cfg Γ Q)
    (hq : p.All (fun a=>Implements M out' (out a) (q a))) :
    Implements M out' c (p.bind q) := by
  induction h with
  | done a => exact hq
  | read c f h ih => exact .read c _ (fun b=>by cases b;exact ih false hq.1;exact ih true hq.2)
  | delay c d n p hs hr ih => exact .delay c d n _ hs (ih hq)
omit [Inhabited Γ] in
lemma seq_supported [Inhabited Γ] (M : Table Γ Q) (N : Table Γ R) (r₀ : R)
    (S : Finset Q) (T : Finset R) (hM : Supported M S) (hN : Supported N T) (hr : r₀∈T) :
    Supported (seq M N r₀) (S.disjSum T) := by
  intro q hq a b q' act he
  cases q with
  | inl q =>
    have hq':q∈S := Finset.inl_mem_disjSum.mp hq
    cases h:M q a b with
    | none => simp only [seq,h,Option.some.injEq,Prod.mk.injEq] at he;rcases he with ⟨rfl,rfl⟩;exact Finset.inr_mem_disjSum.mpr hr
    | some x =>
      rcases x with ⟨v,ac⟩
      simp only [seq,h,Option.some.injEq,Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      exact Finset.inl_mem_disjSum.mpr (hM q hq' a b v ac h)
  | inr r =>
    simp only [seq,Option.map_eq_some_iff] at he
    obtain ⟨⟨r',ac⟩,hh,e⟩:=he
    cases e
    exact Finset.inr_mem_disjSum.mpr (hN r (Finset.inr_mem_disjSum.mp hq) a b r' ac hh)
end MatchingFPRAS.PhysicalPost

end OAI
