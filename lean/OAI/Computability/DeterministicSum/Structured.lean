import Mathlib
import OAI.Computability.DeterministicSum.Machine

namespace OAI

/-! Structured assembly, instruction-exact semantics, initialized-memory frames and loops. -/

namespace DeterministicThreeSum

lemma run_add (w : ℕ) (p : Program) (t u : ℕ) (s : State) :
    run w p (t+u) s = (run w p t s).bind (run w p u) := by
  induction t generalizing s with
  | zero => simp [run]
  | succ t ih =>
    rw [Nat.succ_add,run,run]
    cases step w p s <;> simp only [Option.bind_none,Option.bind_some,ih]

namespace Structured

structure Data where
  registers : ℕ → ℕ
  memory : ℕ → Option ℕ

def state (s : Data) (pc : ℕ) : State := ⟨pc,s.registers,s.memory,none⟩

def operand (w : ℕ) (s : Data) (x : Operand) := readOperand w (state s 0) x

def put (s : Data) (dst value : ℕ) : Data :=
  {s with registers:=Function.update s.registers dst value}

inductive Atom where
  | assign (dst : ℕ) (src : Operand)
  | binary (dst : ℕ) (op : BinOp) (left right : Operand)
  | load (dst : ℕ) (address : Operand)
  | store (address value : Operand)

def Atom.instruction : Atom → Instruction
  | .assign d a => .assign d a
  | .binary d op a b => .binary d op a b
  | .load d a => .load d a
  | .store a b => .store a b

def Atom.eval (w : ℕ) (s : Data) : Atom → Option Data
  | .assign d a => some (put s d (operand w s a))
  | .binary d op a b => (evalBinOp w op (operand w s a) (operand w s b)).map (put s d)
  | .load d a => (s.memory (operand w s a)).map (put s d)
  | .store a b => some {s with memory:=Function.update s.memory (operand w s a) (some (operand w s b))}

def test (w : ℕ) (s : Data) (op : Test) (a b : Operand) : Bool :=
  evalTest op (operand w s a) (operand w s b)

inductive Command where
  | skip
  | atom (a : Atom)
  | seq (a b : Command)
  | ite (op : Test) (a b : Operand) (yes no : Command)
  | loop (op : Test) (a b : Operand) (body : Command)

namespace Command

def size : Command → ℕ
  | .skip => 0
  | .atom _ => 1
  | .seq a b => size a+size b
  | .ite _ _ _ yes no => 2+size yes+size no
  | .loop _ _ _ body => size body+2

def compile : Command → ℕ → List Instruction
  | .skip,_ => []
  | .atom a,_ => [a.instruction]
  | .seq a b,pc => a.compile pc ++ b.compile (pc+a.size)
  | .ite op a b yes no,pc =>
    Instruction.branch op a b (pc+1) (pc+2+yes.size) ::
      (yes.compile (pc+1) ++ [.jump (pc+size (.ite op a b yes no))] ++ no.compile (pc+2+yes.size))
  | .loop op a b body,pc =>
    Instruction.branch op a b (pc+1) (pc+size (.loop op a b body)) ::
      (body.compile (pc+1) ++ [.jump pc])

lemma length_compile (c : Command) (pc : ℕ) : (c.compile pc).length=c.size := by
  induction c generalizing pc <;> simp_all [compile,size]
  omega

inductive Eval (w : ℕ) : Command → Data → ℕ → Data → Prop
  | skip (s) : Eval w .skip s 0 s
  | atom {s t a} (h : a.eval w s=some t) : Eval w (.atom a) s 1 t
  | seq {a b s t u i j} : Eval w a s i t → Eval w b t j u → Eval w (.seq a b) s (i+j) u
  | iteTrue {op a b yes no s t i} : test w s op a b=true → Eval w yes s i t →
      Eval w (.ite op a b yes no) s (1+i+1) t
  | iteFalse {op a b yes no s t i} : test w s op a b=false → Eval w no s i t →
      Eval w (.ite op a b yes no) s (1+i) t
  | loopFalse {op a b body s} : test w s op a b=false → Eval w (.loop op a b body) s 1 s
  | loopTrue {op a b body s t u i j} : test w s op a b=true → Eval w body s i t →
      Eval w (.loop op a b body) t j u → Eval w (.loop op a b body) s (1+i+1+j) u

end Command

def Contains (p : Program) (base : ℕ) (code : List Instruction) : Prop :=
  ∀ i, i<code.length → p[base+i]?=code[i]?

lemma contains_self (p : Program) : Contains p 0 p := by simp [Contains]
lemma Contains.head {p : Program} {pc : ℕ} {a : Instruction} {l : List Instruction}
    (h : Contains p pc (a::l)) : p[pc]?=some a := by
  simpa using h 0 (by simp)
lemma Contains.tail {p : Program} {pc : ℕ} {a : Instruction} {l : List Instruction}
    (h : Contains p pc (a::l)) : Contains p (pc+1) l := by
  intro i hi
  simpa only [List.getElem?_cons_succ,Nat.add_assoc,Nat.add_comm 1 i] using h (i+1) (by simpa using hi)
lemma Contains.left {p : Program} {pc : ℕ} {a b : List Instruction}
    (h : Contains p pc (a++b)) : Contains p pc a := by
  intro i hi
  simpa only [List.getElem?_append_left hi] using h i (hi.trans_le (by simp))
lemma Contains.right {p : Program} {pc : ℕ} {a b : List Instruction}
    (h : Contains p pc (a++b)) : Contains p (pc+a.length) b := by
  intro i hi
  have hh := h (a.length+i) (by simp only [List.length_append]; omega)
  simpa only [List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left,Nat.add_assoc] using hh

lemma step_atom {w : ℕ} {p : Program} {pc : ℕ} {a : Atom} {s t : Data}
    (hc : p[pc]?=some a.instruction) (he : a.eval w s=some t) :
    step w p (state s pc)=some (state t (pc+1)) := by
  cases a <;> simp only [Atom.eval] at he
  · cases he
    simp [step,state,hc,operand,put,putRegister,Atom.instruction,readOperand]
  · simp only [Option.map_eq_some_iff] at he
    obtain ⟨v,hv,rfl⟩ := he
    simp [step,state,hc,operand,put,putRegister,Atom.instruction,readOperand] at *
    simp [hv]
  · simp only [Option.map_eq_some_iff] at he
    obtain ⟨v,hv,rfl⟩ := he
    simp [step,state,hc,operand,put,putRegister,Atom.instruction,readOperand] at *
    simp [hv]
  · cases he
    simp [step,state,hc,operand,Atom.instruction,readOperand]

lemma step_jump {w : ℕ} {p : Program} {pc target : ℕ} (s : Data)
    (hc : p[pc]?=some (.jump target)) :
    step w p (state s pc)=some (state s target) := by simp [step,state,hc]

lemma step_branch {w : ℕ} {p : Program} {pc yes no : ℕ} (s : Data)
    (op : Test) (a b : Operand) (hc : p[pc]?=some (.branch op a b yes no)) :
    step w p (state s pc)=some (state s (if test w s op a b then yes else no)) := by
  simp [step,state,hc,test,operand,readOperand]
  rfl

end Structured
end DeterministicThreeSum

namespace DeterministicThreeSum
lemma run_one_of_step {w : ℕ} {p : Program} {s t : State}
    (h : step w p s=some t) : run w p 1 s=some t := by simp [run,h]
lemma run_comp {w : ℕ} {p : Program} {s t u : State} {i j : ℕ}
    (h : run w p i s=some t) (h' : run w p j t=some u) :
    run w p (i+j) s=some u := by rw [run_add,h]; exact h'

namespace Structured.Command

theorem compile_correct {w : ℕ} {c : Command} {s t : Data} {i : ℕ}
    (he : Eval w c s i t) (p : Program) (pc : ℕ) (hc : Contains p pc (c.compile pc)) :
    run w p i (state s pc)=some (state t (pc+c.size)) := by
  induction he generalizing pc with
  | skip s => simp [run,size]
  | @atom s t a h =>
    simpa only [size] using run_one_of_step (step_atom (hc.head) h)
  | @seq a b s t u i j h h' ih ih' =>
    have hleft : Contains p pc (a.compile pc) := hc.left
    have hright : Contains p (pc+a.size) (b.compile (pc+a.size)) := by
      simpa only [length_compile] using hc.right
    simpa only [size,Nat.add_assoc] using run_comp (ih pc hleft) (ih' (pc+a.size) hright)
  | @iteTrue op a b yes no s t i ht hy ih =>
    have hyes : Contains p (pc+1) (yes.compile (pc+1)) := hc.tail.left.left
    have hj : p[pc+1+yes.size]?=some (.jump (pc+(.ite op a b yes no : Command).size)) := by
      simpa only [length_compile] using hc.tail.left.right.head
    have hbr := step_branch (w:=w) s op a b hc.head
    rw [ht] at hbr
    simp only [↓reduceIte] at hbr
    exact run_comp (run_comp (run_one_of_step hbr) (ih (pc+1) hyes))
      (run_one_of_step (step_jump t hj))
  | @iteFalse op a b yes no s t i ht hn ih =>
    have hno : Contains p (pc+2+yes.size) (no.compile (pc+2+yes.size)) := by
      have hh := hc.tail.right
      simpa only [List.length_append,length_compile,List.length_singleton,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,show (1:ℕ)+1=2 from rfl,←Nat.add_assoc] using hh
    have hbr := step_branch (w:=w) s op a b hc.head
    rw [ht] at hbr
    simp only [Bool.false_eq_true,↓reduceIte] at hbr
    simpa only [size,Nat.add_assoc] using run_comp (run_one_of_step hbr) (ih (pc+2+yes.size) hno)
  | @loopFalse op a b body s ht =>
    have hbr := step_branch (w:=w) s op a b hc.head
    rw [ht] at hbr
    simp only [Bool.false_eq_true,↓reduceIte] at hbr
    exact run_one_of_step hbr
  | @loopTrue op a b body s t u i j ht hb hl ih ih' =>
    have hbody : Contains p (pc+1) (body.compile (pc+1)) := hc.tail.left
    have hj : p[pc+1+body.size]?=some (.jump pc) := by
      simpa only [length_compile] using hc.tail.right.head
    have hbr := step_branch (w:=w) s op a b hc.head
    rw [ht] at hbr
    simp only [↓reduceIte] at hbr
    exact run_comp (run_comp (run_comp (run_one_of_step hbr) (ih (pc+1) hbody))
      (run_one_of_step (step_jump t hj))) (ih' pc hc)

def decisionProgram (c : Command) (result : Operand) : Program :=
  c.compile 0 ++ [.branch .eq result (.literal 0) (c.size+2) (c.size+1),.halt true,.halt false]

lemma decision_compiles {w : ℕ} {c : Command} {s t : Data} {i : ℕ}
    (he : Eval w c s i t) (result : Operand) (_hword : 1<wordModulus w) :
    ∃ final : State,
      run w (c.decisionProgram result) (i+2) (state s 0)=some final ∧
      final.answer=some (decide (operand w t result≠0)) := by
  let p := c.decisionProgram result
  have hc : Contains p 0 (c.compile 0) := (contains_self p).left
  have hh := compile_correct he p 0 hc
  simp only [Nat.zero_add] at hh
  have hbr : p[c.size]?=some (.branch .eq result (.literal 0) (c.size+2) (c.size+1)) := by
    simpa only [length_compile,Nat.zero_add] using (contains_self p).right.head
  have ht : p[c.size+1]?=some (.halt true) := by
    simpa only [length_compile,Nat.zero_add] using (contains_self p).right.tail.head
  have hf : p[c.size+2]?=some (.halt false) := by
    simpa only [length_compile,Nat.zero_add,Nat.add_assoc] using (contains_self p).right.tail.tail.head
  have hbranch := step_branch (w:=w) t .eq result (.literal 0) hbr
  have hz : test w t .eq result (.literal 0)=decide (operand w t result=0) := by
    simp [test,operand,readOperand,state,evalTest]
    rfl
  rw [hz] at hbranch
  by_cases hv : operand w t result=0
  · simp only [hv,decide_true,↓reduceIte] at hbranch
    let final : State := {state t (c.size+2) with answer:=some false}
    have hhalt : step w p (state t (c.size+2))=some final := by simp [step,state,hf,final]
    refine ⟨final,run_comp hh (run_comp (run_one_of_step hbranch) (run_one_of_step hhalt)),?_⟩
    simp [final,hv]
  · simp only [hv,decide_false,Bool.false_eq_true,↓reduceIte] at hbranch
    let final : State := {state t (c.size+1) with answer:=some true}
    have hhalt : step w p (state t (c.size+1))=some final := by simp [step,state,ht,final]
    refine ⟨final,run_comp hh (run_comp (run_one_of_step hbranch) (run_one_of_step hhalt)),?_⟩
    simp [final,hv]
end Structured.Command
end DeterministicThreeSum
namespace DeterministicThreeSum.Structured
open Command

@[ext] lemma Data.ext {s t : Data} (hr : s.registers=t.registers) (hm : s.memory=t.memory) : s=t := by
  cases s; cases t; simp_all

lemma operand_register (w : ℕ) (s : Data) (r : ℕ) :
    operand w s (.register r)=s.registers r % wordModulus w := rfl
lemma operand_literal (w : ℕ) (s : Data) (v : ℕ) :
    operand w s (.literal v)=v % wordModulus w := rfl

lemma loop_iterations {w N : ℕ} {op : Test} {a b : Operand} {body : Command}
    (s : ℕ → Data) (cost : ℕ → ℕ)
    (hyes : ∀ k, k<N → test w (s k) op a b=true)
    (hno : test w (s N) op a b=false)
    (hbody : ∀ k, k<N → Eval w body (s k) (cost k) (s (k+1))) :
    Eval w (.loop op a b body) (s 0) ((∑ k ∈ Finset.range N, (cost k+2))+1) (s N) := by
  have aux : ∀ i t, i+t=N →
      Eval w (.loop op a b body) (s i) ((∑ k ∈ Finset.range t, (cost (i+k)+2))+1) (s N) := by
    intro i t
    induction t generalizing i with
    | zero => intro h; simp only [Nat.add_zero] at h; subst i; simpa using (Eval.loopFalse hno)
    | succ t ih =>
      intro h
      have hi : i<N := by omega
      have hn : i+1+t=N := by omega
      have he := Eval.loopTrue (hyes i hi) (hbody i hi) (ih (i+1) hn)
      have heq : (fun k => cost (i+(k+1))+2) = (fun k => cost (i+1+k)+2) := by
        funext k
        congr 2
        omega
      rw [Finset.sum_range_succ',heq]
      convert he using 1
      simp only [Nat.add_zero]
      omega
  simpa using aux 0 N (by omega)

lemma eval_increment {w r : ℕ} {s : Data} (hr : s.registers r+1<wordModulus w) :
    Eval w (.atom (.binary r .add (.register r) (.literal 1))) s 1
      (put s r (s.registers r+1)) := by
  apply Eval.atom
  have h1 : 1<wordModulus w := by omega
  simp [Atom.eval,operand_register,operand_literal,evalBinOp,
    Nat.mod_eq_of_lt hr,Nat.mod_eq_of_lt (by omega : s.registers r<wordModulus w),Nat.mod_eq_of_lt h1]

def fillCommand (ptr stop value : ℕ) : Command :=
  .loop .lt (.register ptr) (.register stop)
    (.seq (.atom (.store (.register ptr) (.register value)))
      (.atom (.binary ptr .add (.register ptr) (.literal 1))))

def filled (s : Data) (ptr base count v : ℕ) : Data where
  registers := Function.update s.registers ptr (base+count)
  memory := fun a => if base≤a ∧ a<base+count then some v else s.memory a

lemma filled_zero (s : Data) (ptr base v : ℕ) (h : s.registers ptr=base) :
    filled s ptr base 0 v=s := by
  apply Data.ext
  · simp [filled,←h]
  · funext a; simp only [filled,Nat.add_zero]; split <;> rename_i ha
    · omega
    · rfl

theorem fillCommand_correct {w ptr stop value base N v : ℕ} (s : Data)
    (hptr : s.registers ptr=base) (hstop : s.registers stop=base+N)
    (hvalue : s.registers value=v) (hs : stop≠ptr) (hv : value≠ptr)
    (hbound : base+N<wordModulus w) (hvbound : v<wordModulus w) :
    Eval w (fillCommand ptr stop value) s (4*N+1) (filled s ptr base N v) := by
  have hstates (k : ℕ) (hk : k≤N) :
      (filled s ptr base k v).registers ptr=base+k ∧
      (filled s ptr base k v).registers stop=base+N ∧
      (filled s ptr base k v).registers value=v := by
    simp [filled,Function.update_of_ne hs,Function.update_of_ne hv,hstop,hvalue]
  have hyes : ∀ k, k<N → test w (filled s ptr base k v) .lt (.register ptr) (.register stop)=true := by
    intro k hk
    obtain ⟨ha,hb,hc⟩ := hstates k (by omega)
    simp [test,evalTest,operand_register,ha,hb,Nat.mod_eq_of_lt hbound,
      Nat.mod_eq_of_lt (by omega : base+k<wordModulus w)]
    omega
  have hno : test w (filled s ptr base N v) .lt (.register ptr) (.register stop)=false := by
    obtain ⟨ha,hb,hc⟩ := hstates N le_rfl
    simp [test,evalTest,operand_register,ha,hb]
  have hbody : ∀ k, k<N → Eval w
      (.seq (.atom (.store (.register ptr) (.register value)))
       (.atom (.binary ptr .add (.register ptr) (.literal 1))))
      (filled s ptr base k v) 2 (filled s ptr base (k+1) v) := by
    intro k hk
    obtain ⟨ha,hb,hc⟩ := hstates k (by omega)
    let t : Data := {filled s ptr base k v with
      memory:=Function.update (filled s ptr base k v).memory (base+k) (some v)}
    have hs' : Eval w (.atom (.store (.register ptr) (.register value)))
        (filled s ptr base k v) 1 t := by
      apply Eval.atom
      simp [Atom.eval,operand_register,ha,hc,Nat.mod_eq_of_lt hvbound,
        Nat.mod_eq_of_lt (by omega : base+k<wordModulus w),t]
    have ht : t.registers ptr+1<wordModulus w := by change (filled s ptr base k v).registers ptr+1<wordModulus w; rw [ha]; omega
    have hi := eval_increment ht
    have heq : put t ptr (t.registers ptr+1)=filled s ptr base (k+1) v := by
      apply Data.ext
      · simp [put,t,filled,Function.update_idem,Nat.add_assoc]
      · funext a
        simp only [put,t,filled]
        by_cases ha : a=base+k
        · subst a; simp
        · rw [Function.update_of_ne ha]
          by_cases hl : base≤a
          · by_cases hh : a<base+k
            · simp [hl,hh,show a<base+(k+1) by omega]
            · simp [hl,hh,show ¬a<base+(k+1) by omega]
          · simp [hl]
    rw [heq] at hi
    exact Eval.seq hs' hi
  have he := loop_iterations (N:=N) (fun k => filled s ptr base k v) (fun _ => 2) hyes hno hbody
  rw [filled_zero s ptr base v hptr] at he
  simpa [fillCommand,Finset.sum_const,Nat.mul_comm] using he
end DeterministicThreeSum.Structured
namespace DeterministicThreeSum.Structured
open Command

def Atom.writes : Atom → Finset ℕ
  | .assign d _ | .binary d _ _ _ | .load d _ => {d}
  | .store _ _ => ∅

def Command.writes : Command → Finset ℕ
  | .skip => ∅
  | .atom a => a.writes
  | .seq a b => a.writes∪b.writes
  | .ite _ _ _ a b => a.writes∪b.writes
  | .loop _ _ _ body => body.writes

def Atom.noStore : Atom → Prop
  | .store _ _ => False
  | _ => True

def Command.noStore : Command → Prop
  | .skip => True
  | .atom a => a.noStore
  | .seq a b | .ite _ _ _ a b => a.noStore ∧ b.noStore
  | .loop _ _ _ body => body.noStore

lemma atom_register_frame {w r : ℕ} {s t : Data} {a : Atom}
    (he : a.eval w s=some t) (hr : r ∉ a.writes) : t.registers r=s.registers r := by
  cases a <;> simp only [Atom.eval,Option.map_eq_some_iff] at he
  · cases he; simp [put, Function.update_of_ne (by simpa [Atom.writes] using hr)]
  · obtain ⟨v,_,rfl⟩ := he
    simp [put,Function.update_of_ne (by simpa [Atom.writes] using hr)]
  · obtain ⟨v,_,rfl⟩ := he
    simp [put,Function.update_of_ne (by simpa [Atom.writes] using hr)]
  · cases he; rfl

lemma register_frame {w r cost : ℕ} {s t : Data} {c : Command}
    (he : Eval w c s cost t) (hr : r ∉ c.writes) : t.registers r=s.registers r := by
  induction he with
  | skip => rfl
  | atom h => exact atom_register_frame h hr
  | seq h h' ih ih' =>
    simp only [Command.writes,Finset.mem_union,not_or] at hr
    exact (ih' hr.2).trans (ih hr.1)
  | iteTrue _ _ ih => exact ih (by simp only [Command.writes,Finset.mem_union,not_or] at hr; exact hr.1)
  | iteFalse _ _ ih => exact ih (by simp only [Command.writes,Finset.mem_union,not_or] at hr; exact hr.2)
  | loopFalse => rfl
  | loopTrue _ _ _ ih ih' => exact (ih' hr).trans (ih hr)

lemma atom_memory_frame {w : ℕ} {s t : Data} {a : Atom}
    (he : a.eval w s=some t) (hstore : a.noStore) : t.memory=s.memory := by
  cases a <;> simp only [Atom.eval,Option.map_eq_some_iff] at he
  · cases he; rfl
  · obtain ⟨v,_,rfl⟩ := he; rfl
  · obtain ⟨v,_,rfl⟩ := he; rfl
  · exact False.elim hstore

lemma memory_frame {w cost : ℕ} {s t : Data} {c : Command}
    (he : Eval w c s cost t) (hstore : c.noStore) : t.memory=s.memory := by
  induction he with
  | skip => rfl
  | atom h => exact atom_memory_frame h hstore
  | seq h h' ih ih' => exact (ih' hstore.2).trans (ih hstore.1)
  | iteTrue _ _ ih => exact ih hstore.1
  | iteFalse _ _ ih => exact ih hstore.2
  | loopFalse => rfl
  | loopTrue _ _ _ ih ih' => exact (ih' hstore).trans (ih hstore)

theorem bounded_loop {w N B : ℕ} {op : Test} {a b : Operand} {body : Command}
    (Inv : ℕ → Data → Prop)
    (hyes : ∀ k s, k<N → Inv k s → test w s op a b=true)
    (hno : ∀ s, Inv N s → test w s op a b=false)
    (hbody : ∀ k s, k<N → Inv k s → ∃ cost t, Eval w body s cost t ∧ cost≤B ∧ Inv (k+1) t)
    {i : ℕ} (hi : i≤N) {s : Data} (hs : Inv i s) :
    ∃ cost t, Eval w (.loop op a b body) s cost t ∧ cost≤(B+2)*(N-i)+1 ∧ Inv N t := by
  have aux : ∀ fuel i, i+fuel=N → ∀ s, Inv i s →
      ∃ cost t, Eval w (.loop op a b body) s cost t ∧ cost≤(B+2)*fuel+1 ∧ Inv N t := by
    intro fuel
    induction fuel with
    | zero =>
      intro i he s hs
      have hi : i=N := by omega
      subst i
      exact ⟨1,s,Eval.loopFalse (hno s hs),by simp,hs⟩
    | succ fuel ih =>
      intro i he s hs
      have hlt : i<N := by omega
      obtain ⟨c,t,ht,hc,hInv⟩ := hbody i s hlt hs
      obtain ⟨c',u,hu,hc',hInv'⟩ := ih (i+1) (by omega) t hInv
      exact ⟨1+c+1+c',u,Eval.loopTrue (hyes i s hlt hs) ht hu,by nlinarith,hInv'⟩
  exact aux (N-i) i (by omega) s hs

lemma eval_assign {w : ℕ} (s : Data) (r : ℕ) (a : Operand) :
    Eval w (.atom (.assign r a)) s 1 (put s r (operand w s a)) := Eval.atom rfl

lemma eval_load {w r a v : ℕ} {s : Data} (ha : a<wordModulus w) (hv : s.memory a=some v) :
    Eval w (.atom (.load r (.literal a))) s 1 (put s r v) := by
  apply Eval.atom
  simp [Atom.eval,operand_literal,Nat.mod_eq_of_lt ha,hv]
end DeterministicThreeSum.Structured

end OAI
