import OAI.Computability.Scheduling.TreeData

namespace OAI

section

namespace ThreeMachine.StackCompiler

structure Packed (k : ℕ) where
  Control : Type
  finiteControl : Fintype Control
  program : Program k Control

attribute [instance] Packed.finiteControl

namespace Packed
variable {k : ℕ}

def ofProgram {Q : Type} [Fintype Q] (p : Program k Q) : Packed k := ⟨Q,inferInstance,p⟩
def seq (P P' : Packed k) : Packed k := ofProgram (Program.seq P.program P'.program)
def branch (test : Heads k → Bool) (P P' : Packed k) : Packed k :=
  ofProgram (Program.branch test P.program P'.program)
def loop (test : Heads k → Bool) (P : Packed k) : Packed k :=
  ofProgram (Program.loop test P.program)

def Runs (P : Packed k) := P.program.Runs

theorem Runs.seq {P P' : Packed k} {s t u : Store k} {n m : ℕ}
    (h : P.Runs s t n) (h' : P'.Runs t u m) : (P.seq P').Runs s u (n+m+1) :=
  Program.Runs.seq h h'

theorem Runs.mono {P : Packed k} {s t : Store k} {n m : ℕ}
    (h : P.Runs s t n) (hnm : n ≤ m) : P.Runs s t m := Program.Runs.mono h hnm

end Packed

namespace Tree
variable {r : ℕ}
abbrev Registers (r : ℕ) := Fin r → Data

def reg (i : Fin r) : Fin (r+4) := i.castAdd 4
def temp (i : Fin 4) : Fin (r+4) := i.natAdd r

def memory (s : Registers r) : Store (r+3) :=
  Fin.append (m := r) (n := 4) (fun i : Fin r => (s i).encode) (fun _ : Fin 4 => [])

@[simp] theorem memory_reg (s : Registers r) (i : Fin r) : memory s (reg i) = (s i).encode :=
  Fin.append_left _ _ _
@[simp] theorem memory_temp (s : Registers r) (i : Fin 4) : memory s (temp i) = [] :=
  Fin.append_right _ _ _
@[simp] theorem reg_ne_temp (i : Fin r) (j : Fin 4) : reg i ≠ temp j := by
  intro he
  have hv := congrArg Fin.val he
  simp only [reg,temp,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega
@[simp] theorem temp_ne_reg (i : Fin r) (j : Fin 4) : temp j ≠ reg i := (reg_ne_temp i j).symm
@[simp] theorem reg_eq_reg (i j : Fin r) : reg i = reg j ↔ i = j := Fin.castAdd_inj
@[simp] theorem temp_eq_temp (i j : Fin 4) : (temp i : Fin (r+4)) = temp j ↔ i = j := Fin.natAdd_inj r

theorem memory_update (s : Registers r) (dst : Fin r) (d : Data) :
    memory (Function.update s dst d) = Function.update (memory s) (reg dst) d.encode := by
  funext i
  refine Fin.addCases (m := r) (n := 4) (fun i => ?_) (fun i => ?_) i
  · change memory _ (reg i) = Function.update (memory s) (reg dst) d.encode (reg i)
    by_cases hi : i = dst <;> simp [hi]
  · change memory _ (temp i) = Function.update (memory s) (reg dst) d.encode (temp i)
    simp

def nil (dst : Fin r) : Packed (r+3) := Packed.ofProgram (Program.setNil (reg dst))
def pair (dst a b : Fin r) : Packed (r+3) :=
  Packed.ofProgram (Program.setPair (reg dst) (reg a) (reg b) (temp 0) (temp 1))

theorem nil_runs (dst : Fin r) (s : Registers r) :
    (nil dst).Runs (memory s) (memory (Function.update s dst .nil)) (3*(s dst).size+2) := by
  rw [memory_update]
  simpa only [nil,Packed.Runs,Packed.ofProgram,memory_reg,Data.size] using Program.setNil_runs (reg dst) (memory s)

theorem pair_runs (dst a b : Fin r) (s : Registers r) :
    (pair dst a b).Runs (memory s) (memory (Function.update s dst (.pair (s a) (s b))))
      (12*(s a).size+12*(s b).size+3*(s dst).size+14) := by
  rw [memory_update]
  simpa only [pair,Packed.Runs,Packed.ofProgram,memory_reg,Data.size,Data.encode_pair,List.cons_append] using
    Program.setPair_runs (dst := reg dst) (a := reg a) (b := reg b) (tmp := temp 0) (buf := temp 1)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (memory s) (by simp) (by simp)

end Tree
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Tree
variable {r : ℕ}

def work (s : Registers r) (t : Fin 4 → List Bool) : Store (r+3) :=
  Fin.append (m := r) (n := 4) (fun i : Fin r => (s i).encode) t

@[simp] theorem work_reg (s : Registers r) (t : Fin 4 → List Bool) (i : Fin r) :
    work s t (reg i) = (s i).encode := Fin.append_left _ _ _
@[simp] theorem work_temp (s : Registers r) (t : Fin 4 → List Bool) (i : Fin 4) :
    work s t (temp i) = t i := Fin.append_right _ _ _

theorem work_update_temp (s : Registers r) (t : Fin 4 → List Bool) (i : Fin 4) (word : List Bool) :
    Function.update (work s t) (temp i) word = work s (Function.update t i word) := by
  funext j
  refine Fin.addCases (m := r) (n := 4) (fun j => ?_) (fun j => ?_) j
  · change Function.update (work s t) (temp i) word (reg j) = work _ _ (reg j)
    simp
  · change Function.update (work s t) (temp i) word (temp j) = work _ _ (temp j)
    by_cases hj : j = i <;> simp [hj]

theorem work_update_reg (s : Registers r) (t : Fin 4 → List Bool) (i : Fin r) (d : Data) :
    Function.update (work s t) (reg i) d.encode = work (Function.update s i d) t := by
  funext j
  refine Fin.addCases (m := r) (n := 4) (fun j => ?_) (fun j => ?_) j
  · change Function.update (work s t) (reg i) d.encode (reg j) = work _ _ (reg j)
    by_cases hj : j = i <;> simp [hj]
  · change Function.update (work s t) (reg i) d.encode (temp j) = work _ _ (temp j)
    simp

@[simp] theorem work_empty (s : Registers r) : work s ![[],[],[],[]] = memory s := by
  have he : (![[],[],[],[]] : Fin 4 → List Bool) = fun _ => [] := by
    funext i; fin_cases i <;> rfl
  simp only [work,memory,he]

def selectFinish (head : Bool) : Packed (r+3) :=
  if head then Packed.ofProgram (Program.seq (Program.clear (temp 0)) (Program.transfer (temp 2) (temp 0)))
  else Packed.ofProgram (Program.seq (Program.clear (temp 2)) (Program.clear (temp 2)))

def selectPair (head : Bool) (dst : Fin r) : Packed (r+3) :=
  (Packed.ofProgram (Program.instruction (fun _ => Program.popActions (temp 0)))).seq
  ((Packed.ofProgram (Program.push (temp 3) true)).seq
  ((Packed.ofProgram (Program.scan (temp 0) (temp 2) (temp 3))).seq
  ((selectFinish head).seq (Packed.ofProgram (Program.move (temp 0) (reg dst) (temp 1))))))

def selectAux (head : Bool) (dst : Fin r) : Packed (r+3) :=
  Packed.branch (fun h => (h (temp 0)).getD false) (selectPair head dst)
    (Packed.ofProgram (Program.move (temp 0) (reg dst) (temp 1)))

def select (head : Bool) (dst src : Fin r) : Packed (r+3) :=
  (Packed.ofProgram (Program.copy (reg src) (temp 0) (temp 1))).seq (selectAux head dst)

theorem selectFinish_runs (head : Bool) (s : Registers r) (a b : Data) :
    (selectFinish head).Runs (work s ![b.encode,[],a.encode.reverse,[]])
      (work s ![(if head then a else b).encode,[],[],[]]) (3*a.size+3*b.size+2) := by
  cases head with
  | false =>
    have h₁ := (Program.clear_exec (temp 2) (work s ![b.encode,[],a.encode.reverse,[]])).runs
    rw [work_update_temp] at h₁
    have he : Function.update ![b.encode,[],a.encode.reverse,[]] (2 : Fin 4) [] = ![b.encode,[],[],[]] := by
      funext i; fin_cases i <;> simp
    rw [he] at h₁
    have h₂ := (Program.clear_exec (temp 2) (work s ![b.encode,[],[],[]])).runs
    rw [work_update_temp] at h₂
    have he₂ : Function.update ![b.encode,[],[],[]] (2 : Fin 4) [] = ![b.encode,[],[],[]] := by
      funext i; fin_cases i <;> simp
    rw [he₂] at h₂
    have hx := h₁.seq h₂
    exact hx.mono (by simp [Data.size]; omega)
  | true =>
    have h₁ := (Program.clear_exec (temp 0) (work s ![b.encode,[],a.encode.reverse,[]])).runs
    rw [work_update_temp] at h₁
    have he : Function.update ![b.encode,[],a.encode.reverse,[]] (0 : Fin 4) [] = ![[],[],a.encode.reverse,[]] := by
      funext i; fin_cases i <;> simp
    rw [he] at h₁
    have h₂ := (Program.transfer_exec (show (temp 2 : Fin (r+4)) ≠ temp 0 by simp)
      (work s ![[],[],a.encode.reverse,[]])).runs
    have he₂ : Program.transferResult (temp 2) (temp 0) (work s ![[],[],a.encode.reverse,[]]) =
        work s ![a.encode,[],[],[]] := by
      simp only [Program.transferResult,work_temp,Matrix.cons_val_two,Matrix.cons_val_zero,
        List.append_nil,work_update_temp]
      congr 1
      funext i; fin_cases i <;> simp
    rw [he₂] at h₂
    exact (h₁.seq h₂).mono (by simp [Data.size]; omega)

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Tree
variable {r : ℕ}

theorem selectPair_runs (head : Bool) (dst : Fin r) (s : Registers r) (a b : Data) :
    (selectPair head dst).Runs (work s ![(Data.pair a b).encode,[],[],[]])
      (memory (Function.update s dst (if head then a else b)))
      (30*(a.size+b.size+(s dst).size+1)) := by
  let s₀ := work s ![(Data.pair a b).encode,[],[],[]]
  let s₁ := work s ![a.encode++b.encode,[],[],[]]
  let s₂ := work s ![a.encode++b.encode,[],[],[true]]
  let s₃ := work s ![b.encode,[],a.encode.reverse,[]]
  let s₄ := work s ![(if head then a else b).encode,[],[],[]]
  have h₁ : (Packed.ofProgram (Program.instruction (fun _ => Program.popActions (temp 0)))).Runs s₀ s₁ 1 := by
    have hh := (Program.pop_instruction (temp 0) s₀).runs
    have he : Function.update s₀ (temp 0) (s₀ (temp 0)).tail = s₁ := by
      simp only [s₀,s₁,work_temp,Matrix.cons_val_zero,Data.encode_pair,work_update_temp]
      congr 1
      funext i; fin_cases i <;> simp
    rwa [he] at hh
  have h₂ : (Packed.ofProgram (Program.push (temp 3) true)).Runs s₁ s₂ 1 := by
    have hh := (Program.push_exec (temp 3) true s₁).runs
    have he : Function.update s₁ (temp 3) (true :: s₁ (temp 3)) = s₂ := by
      simp only [s₁,s₂,work_temp,Matrix.cons_val_three,work_update_temp]
      congr 1
      funext i; fin_cases i <;> simp
    rwa [he] at hh
  have h₃ : (Packed.ofProgram (Program.scan (temp 0) (temp 2) (temp 3))).Runs s₂ s₃ (3*a.size) := by
    have hh := (Program.scan_tree (src := temp 0) (dst := temp 2) (ct := temp 3)
      (by simp) (by simp) (by simp) a s₂ b.encode (by simp [s₂]) (by simp [s₂])).runs
    have he : Program.scanned (temp 0) (temp 2) (temp 3) s₂ b.encode a.encode 0 = s₃ := by
      simp only [Program.scanned,s₂,s₃,work_temp,Matrix.cons_val_two,
        List.replicate_zero,work_update_temp]
      congr 1
      funext i; fin_cases i <;> simp
    rwa [he] at hh
  have h₄ : (selectFinish head).Runs s₃ s₄ (3*a.size+3*b.size+2) :=
    selectFinish_runs head s a b
  have h₅ : (Packed.ofProgram (Program.move (temp 0) (reg dst) (temp 1))).Runs s₄
      (memory (Function.update s dst (if head then a else b)))
      (3*(s dst).size+6*(if head then a else b).size+2) := by
    have hh := (Program.move_exec (src := temp 0) (dst := reg dst) (tmp := temp 1)
      (by simp) (by simp) (by simp) s₄ (by simp [s₄])).runs
    have he : Function.update s₄ (temp 0) [] = memory s := by
      simp only [s₄,work_update_temp]
      have hw : Function.update ![(if head then a else b).encode,[],[],[]] (0 : Fin 4) [] = ![[],[],[],[]] := by
        funext i; fin_cases i <;> simp
      rw [hw,work_empty]
    rw [he] at hh
    simpa only [Packed.Runs,Packed.ofProgram,s₄,work_reg,work_temp,Matrix.cons_val_zero,← memory_update,Data.size] using hh
  apply (h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))).mono
  cases head <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem selectAux_runs (head : Bool) (dst : Fin r) (s : Registers r) (d : Data) :
    (selectAux head dst).Runs (work s ![d.encode,[],[],[]])
      (memory (Function.update s dst (if head then d.head else d.tail)))
      (40*(d.size+(s dst).size+1)) := by
  cases d with
  | nil =>
    have hh := (Program.move_exec (src := temp 0) (dst := reg dst) (tmp := temp 1)
      (by simp) (by simp) (by simp) (work s ![Data.nil.encode,[],[],[]]) (by simp)).runs
    have he : Function.update (work s ![Data.nil.encode,[],[],[]]) (temp 0) [] = memory s := by
      rw [work_update_temp]
      have hw : Function.update ![Data.nil.encode,[],[],[]] (0 : Fin 4) [] = ![[],[],[],[]] := by
        funext i; fin_cases i <;> simp
      rw [hw,work_empty]
    rw [he] at hh
    have hx := hh.branch_right (fun h => (h (temp 0)).getD false) (selectPair head dst).program (by simp)
    have hout : (if head then Data.nil.head else Data.nil.tail) = Data.nil := by cases head <;> rfl
    rw [hout,memory_update]
    simpa only [selectAux,Packed.Runs,Packed.branch,Packed.ofProgram,work_temp,Matrix.cons_val_zero] using
      hx.mono (m := 40*(Data.nil.size+(s dst).size+1)) (by simp [Data.size]; omega)
  | pair a b =>
    have hh := selectPair_runs head dst s a b
    have hx := Program.Runs.branch_left (fun h => (h (temp 0)).getD false)
      (Program.move (temp 0) (reg dst) (temp 1)) hh (by simp [Data.encode_pair])
    exact hx.mono (by simp [Data.size_pair]; omega)

theorem select_runs (head : Bool) (dst src : Fin r) (s : Registers r) :
    (select head dst src).Runs (memory s)
      (memory (Function.update s dst (if head then (s src).head else (s src).tail)))
      (50*((s src).size+(s dst).size+1)) := by
  have h₁ := (Program.copy_exec (src := reg src) (dst := temp 0) (tmp := temp 1)
    (by simp) (by simp) (by simp) (memory s) (by simp)).runs
  have he : Function.update (memory s) (temp 0) (memory s (reg src)) = work s ![(s src).encode,[],[],[]] := by
    rw [memory_reg,← work_empty,work_update_temp]
    congr 1
    funext i; fin_cases i <;> simp
  rw [he] at h₁
  have h₂ := selectAux_runs head dst s (s src)
  exact (h₁.seq h₂).mono (by simp [Data.size]; omega)

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ} {Q : Type}

theorem Runs.loop_stop (test : Heads k → Bool) (P : Program k Q) (s : Store k)
    (hs : test (fun i => (s i).head?) = false) : (loop test P).Runs s s 0 :=
  (Program.loop_stop test P s hs).runs

theorem Runs.loop_iterate (test : Heads k → Bool) {P : Program k Q}
    {s t u : Store k} {n m : ℕ} (h : P.Runs s t n) (h' : (loop test P).Runs t u m)
    (hs : test (fun i => (s i).head?) = true) : (loop test P).Runs s u (n+m+2) := by
  obtain ⟨n',hn,q,hq⟩ := h
  obtain ⟨m',hm,r,hr⟩ := h'
  have hnone : r = none := by
    have hh := hr.halted
    cases r with
    | none => rfl
    | some q =>
      unfold step at hh
      cases he : P.transition q (fun i => (u i).head?) <;> simp_all [loop]
  subst r
  exact (Program.loop_iterate test hs hq hr).runs.mono (by omega)

end ThreeMachine.StackCompiler.Program

namespace ThreeMachine.StackCompiler.Tree
variable {r : ℕ}

def skip : Packed (r+3) := Packed.ofProgram (Program.instruction (fun _ => Program.stayActions))

theorem skip_runs (s : Registers r) : skip.Runs (memory s) (memory s) 1 := by
  have hh := (Program.instruction_exec (k := r+3) (fun _ => Program.stayActions) (memory s)).runs
  simpa only [skip,Packed.Runs,Packed.ofProgram,Program.stayActions,Action.apply] using hh

def copy (dst src : Fin r) : Packed (r+3) :=
  if dst = src then skip else Packed.ofProgram (Program.copy (reg src) (reg dst) (temp 0))

theorem copy_runs (dst src : Fin r) (s : Registers r) :
    (copy dst src).Runs (memory s) (memory (Function.update s dst (s src)))
      (3*(s dst).size+6*(s src).size+2) := by
  by_cases he : dst = src
  · subst src
    simpa [copy] using (skip_runs s).mono (by omega : 1 ≤ 3*(s dst).size+6*(s dst).size+2)
  · rw [memory_update]
    unfold copy
    rw [ite_eq_right he]
    have hh := (Program.copy_exec (src := reg src) (dst := reg dst) (tmp := temp 0)
      (by simpa using Ne.symm he) (by simp) (by simp) (memory s) (by simp)).runs
    simpa only [memory_reg,Data.size,Packed.Runs,Packed.ofProgram] using hh

def weight (s : Registers r) : ℕ := 1 + ∑ i, (s i).size

theorem one_le_weight (s : Registers r) : 1 ≤ weight s := by unfold weight; omega

theorem size_le_weight (s : Registers r) (i : Fin r) : (s i).size ≤ weight s := by
  have hh : (s i).size ≤ ∑ j, (s j).size := Finset.single_le_sum (f := fun j : Fin r => (s j).size) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  unfold weight
  omega

inductive Code (V : Type)
  | skip
  | nil (dst : V)
  | pair (dst a b : V)
  | select (head : Bool) (dst src : V)
  | copy (dst src : V)
  | seq (first second : Code V)
  | branch (src : V) (nonempty empty : Code V)
  | loop (src : V) (body : Code V)

def _root_.OAI.ThreeMachine.StackCompiler.Data.nonempty : Data → Bool | .nil => false | .pair _ _ => true

@[simp] theorem _root_.OAI.ThreeMachine.StackCompiler.Data.encode_head (d : Data) : d.encode.head?.getD false = d.nonempty := by
  cases d <;> rfl

inductive Eval {V : Type} [DecidableEq V] : Code V → (V → Data) → (V → Data) → ℕ → Prop
  | skip (s) : Eval .skip s s 1
  | nil (dst) (s) : Eval (.nil dst) s (Function.update s dst .nil) (1+(s dst).size)
  | pair (dst a b) (s) : Eval (.pair dst a b) s (Function.update s dst (.pair (s a) (s b))) (1+(s dst).size+(s a).size+(s b).size)
  | select (head dst src) (s) :
      Eval (.select head dst src) s (Function.update s dst (if head then (s src).head else (s src).tail)) (1+(s dst).size+(s src).size)
  | copy (dst src) (s) : Eval (.copy dst src) s (Function.update s dst (s src)) (1+(s dst).size+(s src).size)
  | seq {p q s t u n m} : Eval p s t n → Eval q t u m → Eval (.seq p q) s u (n+m+1)
  | branch_true {src p q s t n} : (s src).nonempty = true → Eval p s t n → Eval (.branch src p q) s t (n+1)
  | branch_false {src p q s t n} : (s src).nonempty = false → Eval q s t n → Eval (.branch src p q) s t (n+1)
  | loop_stop {src p s} : (s src).nonempty = false → Eval (.loop src p) s s 1
  | loop_step {src p s t u n m} : (s src).nonempty = true → Eval p s t n →
      Eval (.loop src p) t u m → Eval (.loop src p) s u (n+m+1)

namespace Code

def compile : Code (Fin r) → Packed (r+3)
  | .skip => Tree.skip
  | .nil dst => Tree.nil dst
  | .pair dst a b => Tree.pair dst a b
  | .select head dst src => Tree.select head dst src
  | .copy dst src => Tree.copy dst src
  | .seq p q => p.compile.seq q.compile
  | .branch src p q => Packed.branch (fun h => (h (reg src)).getD false) p.compile q.compile
  | .loop src p => Packed.loop (fun h => (h (reg src)).getD false) p.compile

end Code

theorem Eval.compile {p : Code (Fin r)} {s t : Registers r} {n : ℕ} (h : Eval p s t n) :
    p.compile.Runs (memory s) (memory t) (150*n) := by
  induction h with
  | skip s => exact (skip_runs s).mono (by omega)
  | nil dst s =>
    apply (nil_runs dst s).mono
    omega
  | pair dst a b s =>
    apply (pair_runs dst a b s).mono
    omega
  | select head dst src s =>
    apply (select_runs head dst src s).mono
    omega
  | copy dst src s =>
    apply (copy_runs dst src s).mono
    omega
  | seq _ _ ih ih' => exact (ih.seq ih').mono (by omega)
  | @branch_true src p q s t n hs _ ih =>
    exact (Program.Runs.branch_left _ q.compile.program ih (by simpa using hs)).mono (by omega)
  | @branch_false src p q s t n hs _ ih =>
    exact (Program.Runs.branch_right _ p.compile.program ih (by simpa using hs)).mono (by omega)
  | @loop_stop src p s hs =>
    exact (Program.Runs.loop_stop _ p.compile.program (memory s) (by simpa using hs)).mono (by omega)
  | @loop_step src p s t u n m hs _ _ ih ih' =>
    exact (Program.Runs.loop_iterate _ ih ih' (by simpa using hs)).mono (by omega)

end ThreeMachine.StackCompiler.Tree

end

end OAI
