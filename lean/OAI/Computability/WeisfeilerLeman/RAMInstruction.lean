import OAI.Computability.WeisfeilerLeman.RAMMemory

namespace OAI

namespace WLTime.ZeroTest
open TypedStack
abbrev Reg := Fin 2
def state (input flags : List Bool) : Stacks Reg Bool := ![input,flags]
def marks : List Bool → Bool → List Bool → List Bool
  | [],b,hist => b::hist
  | x::xs,b,hist => marks xs (b||x) (b::hist)
 theorem marks_length (xs : List Bool) (b : Bool) (hist : List Bool) :
    (marks xs b hist).length=xs.length+hist.length+1 := by
  induction xs generalizing b hist with
  | nil => simp [marks]
  | cons x xs ih => simp [marks,ih]; omega
 theorem marks_head (xs : List Bool) (b : Bool) (hist : List Bool) :
    (marks xs b hist).headD false=(b||xs.any id) := by
  induction xs generalizing b hist with
  | nil => simp [marks]
  | cons x xs ih =>
    change (marks xs (b||x) (b::hist)).headD false=(b||(x::xs).any id)
    rw [ih]
    simp only [List.any_cons, Bool.or_assoc, id_eq]
def body : Code Reg Bool := .seq (.pushDyn 1 (fun v => (v 1).getD false || (v 0).getD false)) (.pop 0)
def loopCode : Code Reg Bool := .loop (Code.nonempty 0) body
def finish : Code Reg Bool := .branch (fun v : Tops Reg Bool => (v 1).getD false)
  (.seq (.clear 1) (.push 1 true)) (.seq (.clear 1) (.push 1 false))
def program : Code Reg Bool := .seq (.push 1 false) (.seq loopCode finish)
 theorem loop_exec (xs : List Bool) (b : Bool) (hist : List Bool) :
    loopCode.Exec (state xs (b::hist)) (5*xs.length+1) (state [] (marks xs b hist)) := by
  induction xs generalizing b hist with
  | nil => exact Code.Exec.loop_false (by simp [Code.nonempty,tops,state])
  | cons x xs ih =>
    let s₀ := state (x::xs) (b::hist)
    let s₁ := Function.update s₀ 1 ((b||x)::b::hist)
    have hp : (Code.pushDyn 1 (fun v : Tops Reg Bool => (v 1).getD false || (v 0).getD false)).Exec s₀ 2 s₁ := by
      simpa [s₀,s₁,state,tops] using Code.Exec.pushDyn s₀ 1 (fun v : Tops Reg Bool => (v 1).getD false || (v 0).getD false)
    have he : (Code.pop 0).Exec s₁ 2 (state xs ((b||x)::b::hist)) := by
      have h := Code.Exec.pop s₁ 0
      convert h using 1
      funext i; fin_cases i <;> simp [s₁,s₀,state]
    have hh := Code.Exec.loop_true (p:=Code.nonempty (0 : Reg)) (by simp [Code.nonempty,tops,s₀,state])
      (Code.Exec.seq hp he) (ih (b||x) (b::hist))
    convert hh using 1 <;> try rfl
    simp only [List.length_cons]; omega
 theorem finish_exec (fs : List Bool) :
    finish.Exec (state [] fs) (3*fs.length+4) (state [] [fs.headD false]) := by
  have hc : (Code.clear 1).Exec (state [] fs) (3*fs.length+1) (state [] []) := by
    have he := Code.clear_exec (1 : Reg) (state [] fs)
    convert he using 1 <;> try rfl
    funext k; fin_cases k <;> simp [state]
  have hp (b : Bool) : (Code.push 1 b).Exec (state [] []) 2 (state [] [b]) := by
    have he := Code.Exec.push (state [] [] : Stacks Reg Bool) 1 b
    convert he using 1
    funext k; fin_cases k <;> simp [state]
  cases hh : fs.headD false
  · have he := Code.Exec.branch_false (a:=.seq (.clear 1) (.push 1 true)) (p:=fun v : Tops Reg Bool => (v 1).getD false)
      (by simpa [tops,state] using hh) (Code.Exec.seq hc (hp false))
    simpa only [finish,hh,Nat.add_assoc] using he
  · have he := Code.Exec.branch_true (b:=.seq (.clear 1) (.push 1 false)) (p:=fun v : Tops Reg Bool => (v 1).getD false)
      (by simpa [tops,state] using hh) (Code.Exec.seq hc (hp true))
    simpa only [finish,hh,Nat.add_assoc] using he
 theorem program_exec (xs : List Bool) :
    program.Exec (state xs []) (8*xs.length+10) (state [] [xs.any id]) := by
  have hp : (Code.push 1 false).Exec (state xs []) 2 (state xs [false]) := by
    have he := Code.Exec.push (state xs [] : Stacks Reg Bool) 1 false
    convert he using 1
    funext k; fin_cases k <;> simp [state]
  have he := loop_exec xs false []
  have hf := finish_exec (marks xs false [])
  rw [marks_head,marks_length] at hf
  simp only [Bool.false_or,List.length_nil,Nat.add_zero] at hf
  have hg := Code.Exec.seq hp (Code.Exec.seq he hf)
  convert hg using 1
  · rfl
  · omega
 theorem program_size : program.controlSize=18 := by rfl
 theorem any_false_iff (xs : List Bool) : xs.any id=false ↔ xs=List.replicate xs.length false := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases x <;> simp [List.replicate_succ,ih]
 theorem word_zero_iff {w : ℕ} (a : Word w) : (wordBits a).any id=false ↔ a.val=0 := by
  rw [any_false_iff]
  constructor
  · intro h
    have he : wordBits a=wordBits (⟨0,by positivity⟩ : Word w) := by
      rw [WordMemory.word_zero]
      simpa [wordBits] using h
    exact congrArg Fin.val (BitWords.word_injective he)
  · intro h
    have he : a=(⟨0,by positivity⟩ : Word w) := Fin.ext h
    rw [he,WordMemory.word_zero]
    simp
end WLTime.ZeroTest

namespace WLTime.RAMInstruction
 def operations {R P : ℕ} : RAMInstruction R P → List (WordOperation R)
  | .halt _ | .jump _ => []
  | .compute op next => op::operations next
  | .load _ _ next | .store _ _ next => operations next
  | .branchZero _ yes no => operations yes++operations no
 def depth {R P : ℕ} : RAMInstruction R P → ℕ
  | .halt _ | .jump _ => 1
  | .compute _ next | .load _ _ next | .store _ _ next => depth next+1
  | .branchZero _ yes no => max (depth yes) (depth no)+1
 theorem depth_pos {R P : ℕ} (I : RAMInstruction R P) : 0<I.depth := by cases I <;> simp [depth]
end WLTime.RAMInstruction
namespace WLTime.SparseRAM
open WordMemory
structure Config (R P w : ℕ) where
  pc : Fin P
  registers : Fin R → Word w
  log : Log w
  answer : Option Bool

def execute {R P w : ℕ} : RAMInstruction R P → Config R P w → Config R P w
  | .halt b,C => {C with answer := some b}
  | .jump pc,C => {C with pc := pc}
  | .compute op next,C => execute next {C with registers := op.apply w C.registers}
  | .load dest addr next,C => execute next {C with registers := Function.update C.registers dest (read (C.registers addr) C.log)}
  | .store addr src next,C => execute next {C with log := (C.registers addr,C.registers src)::C.log}
  | .branchZero reg yes no,C => if (C.registers reg).val=0 then execute yes C else execute no C
 theorem execute_log_length {R P w : ℕ} (I : RAMInstruction R P) (C : Config R P w) :
    (execute I C).log.length ≤ C.log.length+I.depth := by
  induction I generalizing C with
  | halt b => simp [execute,RAMInstruction.depth]
  | jump pc => simp [execute,RAMInstruction.depth]
  | compute op next ih =>
    have h := ih {C with registers := op.apply w C.registers}
    simpa only [execute,RAMInstruction.depth] using h.trans (by dsimp; omega)
  | load dest addr next ih =>
    have h := ih {C with registers := Function.update C.registers dest (read (C.registers addr) C.log)}
    exact h.trans (by change C.log.length+next.depth ≤ C.log.length+(next.depth+1); omega)
  | store addr src next ih =>
    have h := ih {C with log := (C.registers addr,C.registers src)::C.log}
    simpa only [execute,RAMInstruction.depth,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  | branchZero reg yes no ih ih' =>
    by_cases hz : (C.registers reg).val=0
    · simpa only [execute,ite_eq_left hz,RAMInstruction.depth] using (ih C).trans (by omega)
    · simpa only [execute,ite_eq_right hz,RAMInstruction.depth] using (ih' C).trans (by omega)
 def forget (A : RAM) (n : ℕ) (C : Config A.registers A.locations (A.width.bits n)) : A.Config n where
  pc := C.pc
  registers := C.registers
  memory := fun q => read q C.log
  answer := C.answer
 theorem execute_forget (A : RAM) (n : ℕ) (I : RAMInstruction A.registers A.locations)
    (C : Config A.registers A.locations (A.width.bits n)) :
    A.execute I (forget A n C)=forget A n (execute I C) := by
  induction I generalizing C with
  | halt b => rfl
  | jump pc => rfl
  | compute op next ih => exact ih {C with registers := op.apply (A.width.bits n) C.registers}
  | load dest addr next ih => exact ih {C with registers := Function.update C.registers dest (read (C.registers addr) C.log)}
  | store addr src next ih =>
    have h := ih {C with log := (C.registers addr,C.registers src)::C.log}
    simpa only [execute,RAM.execute,forget,read_prepend] using h
  | branchZero reg yes no ih ih' =>
    by_cases hz : (C.registers reg).val=0
    · simpa [execute,RAM.execute,forget,hz] using ih C
    · simpa [execute,RAM.execute,forget,hz] using ih' C
 def step (A : RAM) (w : ℕ) (C : Config A.registers A.locations w) : Config A.registers A.locations w :=
  match C.answer with
  | some _ => C
  | none => execute (A.program C.pc) C
 theorem step_forget (A : RAM) (n : ℕ) (C : Config A.registers A.locations (A.width.bits n)) :
    A.step (forget A n C)=forget A n (step A (A.width.bits n) C) := by
  cases h : C.answer with
  | none => simpa only [RAM.step,step,forget,h] using execute_forget A n (A.program C.pc) C
  | some b => simp only [RAM.step,step,forget,h]
 theorem iterate_forget (A : RAM) (n : ℕ) (C : Config A.registers A.locations (A.width.bits n)) (t : ℕ) :
    A.step^[t] (forget A n C)=forget A n ((step A (A.width.bits n))^[t] C) := by
  induction t generalizing C with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply,Function.iterate_succ_apply,step_forget,ih]
 theorem step_fixed (A : RAM) (w : ℕ) (C : Config A.registers A.locations w) (h : C.answer.isSome=true) :
    step A w C=C := by cases hh : C.answer <;> simp_all [step]
end WLTime.SparseRAM
namespace WLTime.RAM
 theorem time_halted (A : RAM) (n : ℕ) (input : List Bool) (h : A.halts n input) :
    (A.run n input (A.time n input)).answer.isSome=true := by
  unfold time
  rw [dite_eq_left h]
  exact Nat.find_spec h
 theorem answer_stable (A : RAM) {n : ℕ} (C : A.Config n) (b : Bool) (h : C.answer=some b) : A.step C=C := by simp [step,h]
 theorem run_add_halted (A : RAM) (n : ℕ) (input : List Bool) (t s : ℕ) (h : (A.run n input t).answer.isSome=true) :
    A.run n input (t+s)=A.run n input t := by
  have hh : A.step (A.run n input t)=A.run n input t := by
    cases he : (A.run n input t).answer <;> simp_all [step]
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.add_succ]
    have hr : A.run n input (t+s+1)=A.step (A.run n input (t+s)) := Function.iterate_succ_apply' _ _ _
    rw [hr,ih,hh]
 theorem accepts_iff_answer (A : RAM) (n : ℕ) (input : List Bool) (t : ℕ) (b : Bool)
    (h : (A.run n input t).answer=some b) : A.accepts n input ↔ b=true := by
  constructor
  · rintro ⟨s,hs⟩
    have ht : (A.run n input t).answer.isSome=true := by rw [h]; rfl
    have hu : (A.run n input s).answer.isSome=true := by rw [hs]; rfl
    have he₁ := A.run_add_halted n input t s ht
    have he₂ := A.run_add_halted n input s t hu
    rw [Nat.add_comm] at he₂
    have he := congrArg Config.answer (he₁.symm.trans he₂)
    rw [h,hs] at he
    exact Option.some.inj he
  · intro hb
    exact ⟨t,by rw [h,hb]⟩
end WLTime.RAM

namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
def operations : List (WordOperation A.registers) :=
  (List.ofFn A.program).flatMap RAMInstruction.operations
abbrev Index := Fin (operations A).length
def operation (i : Index A) : WordOperation A.registers := (operations A).get i
abbrev Reg := Fin 14 ⊕ ((i : Index A) × TMPort.Reg (operation A i).implementation)
abbrev Letter := Bool ⊕ (Fin A.locations ⊕ ((i : Index A) × TMTransducer.Letter (operation A i).implementation))
def decode : Letter A → Bool
  | .inl b => b
  | .inr _ => false
def memMap (i : RAMMemory.Reg) : Reg A := .inl ⟨i.val,by omega⟩
theorem memMap_inj : Function.Injective (memMap A) := by
  intro i j h
  exact Fin.ext (congrArg (fun r : Reg A => match r with | .inl k => k.val | .inr _ => 0) h)
def liftMem (s : Stacks RAMMemory.Reg Bool) (pc : Fin A.locations) (answer : Option Bool) : Stacks (Reg A) (Letter A)
  | .inl i => if h : i.val<12 then (s ⟨i.val,h⟩).map Sum.inl
      else if i=12 then [.inr (.inl pc)] else answer.toList.map Sum.inl
  | .inr _ => []
def state {w : ℕ} (C : SparseRAM.Config A.registers A.locations w) : Stacks (Reg A) (Letter A) :=
  liftMem A (RAMMemory.state (registerBits C.registers) (SparseLookup.flatten (WordMemory.entries C.log)) [] []) C.pc C.answer
 theorem liftMem_mem (s : Stacks RAMMemory.Reg Bool) (pc : Fin A.locations) (answer : Option Bool) (i : RAMMemory.Reg) :
    liftMem A s pc answer (memMap A i)=(s i).map Sum.inl := by simp [liftMem,memMap,i.isLt]
 theorem mem_exec {s out : Stacks RAMMemory.Reg Bool} {c : Code RAMMemory.Reg Bool} {t : ℕ}
    (he : c.Exec s t out) (pc : Fin A.locations) (answer : Option Bool) :
    ((c.mapLetters Sum.inl (decode A)).relabel (memMap A)).Exec (liftMem A s pc answer) t (liftMem A out pc answer) := by
  have h := Code.mapLetters_exec (Sum.inl : Bool → Letter A) (decode A) (by intro b; rfl) he
  apply Code.relabel_exec_of_maps _ (memMap_inj A) h
  · intro i; exact liftMem_mem A s pc answer i
  · intro i; exact liftMem_mem A out pc answer i
  · intro r hr
    cases r with
    | inl i =>
      by_cases hi : i.val<12
      · exact False.elim (hr ⟨i.val,hi⟩ rfl)
      · simp [liftMem,hi]
    | inr r => rfl
 def opReg (i : Index A) (r : TMPort.Reg (operation A i).implementation) : Reg A :=
  if r=TMPort.port (operation A i).implementation then .inl 0 else .inr ⟨i,r⟩
 theorem opReg_inj (i : Index A) : Function.Injective (opReg A i) := by
  intro r s h
  by_cases hr : r=TMPort.port (operation A i).implementation
  · by_cases hs : s=TMPort.port (operation A i).implementation
    · exact hr.trans hs.symm
    · simp [opReg,hr,hs] at h
  · by_cases hs : s=TMPort.port (operation A i).implementation
    · simp [opReg,hr,hs] at h
    · simpa [opReg,hr,hs] using h
 def opLetter (i : Index A) : TMPort.Letter (operation A i).implementation → Letter A
  | .inl b => .inl b
  | .inr c => .inr (.inr ⟨i,c⟩)
 theorem opLetter_inj (i : Index A) : Function.Injective (opLetter A i) := by
  intro x y h
  cases x <;> cases y <;> simp_all [opLetter]
 def opDecode (i : Index A) : Letter A → TMPort.Letter (operation A i).implementation :=
  Function.invFun (opLetter A i)
 theorem opDecode_left (i : Index A) : Function.LeftInverse (opDecode A i) (opLetter A i) :=
  Function.leftInverse_invFun (opLetter_inj A i)
 def opCode (i : Index A) (n o : ℕ) : Code (Reg A) (Letter A) :=
  (((TMPort.program (operation A i).implementation n o).mapLetters (opLetter A i) (opDecode A i)).relabel (opReg A i))
 def fileState (file log : List Bool) (pc : Fin A.locations) (answer : Option Bool) : Stacks (Reg A) (Letter A) :=
  liftMem A (RAMMemory.state file log [] []) pc answer
 theorem fileState_opReg (i : Index A) (xs log : List Bool) (pc : Fin A.locations) (answer : Option Bool)
    (r : TMPort.Reg (operation A i).implementation) :
    fileState A xs log pc answer (opReg A i r)=
    Code.listMap (opLetter A i) (TMPort.inputState (operation A i).implementation xs) r := by
  by_cases h : r=TMPort.port (operation A i).implementation
  · subst r
    simp [fileState,liftMem,RAMMemory.state,opReg,TMPort.inputState,Code.listMap,opLetter,List.map_map,Function.comp_def]
  · simp [fileState,liftMem,opReg,h,TMPort.inputState,Code.listMap]
 theorem op_exec (i : Index A) (input output log : List Bool) (pc : Fin A.locations) (answer : Option Bool)
    (ho : (operation A i).implementation.outputs input output) :
    ∃u ≤ TMPort.factor (operation A i).implementation*(input.length+(operation A i).implementation.time input+output.length+1),
      (opCode A i input.length output.length).Exec (fileState A input log pc answer) u (fileState A output log pc answer) := by
  obtain ⟨u,hu,he⟩ := TMPort.program_exec _ input output ho
  refine ⟨u,hu,?_⟩
  have hh := Code.mapLetters_exec (opLetter A i) (opDecode A i) (opDecode_left A i) he
  apply Code.relabel_exec_of_maps _ (opReg_inj A i) hh
  · exact fileState_opReg A i input log pc answer
  · exact fileState_opReg A i output log pc answer
  · intro r hr
    cases r with
    | inl k =>
      have hk : k≠0 := by
        intro h; subst k
        exact hr (TMPort.port _) (by simp [opReg])
      fin_cases k <;> simp_all [fileState,liftMem,RAMMemory.state]
    | inr r => rfl
 theorem opCode_size (i : Index A) (n o : ℕ) :
    (opCode A i n o).controlSize ≤ TMPort.sizeFactor (operation A i).implementation*(n+o+1) := by
  simpa [opCode] using TMPort.program_size (operation A i).implementation n o
 theorem mem_program (pc : Fin A.locations) : ∀op ∈ (A.program pc).operations, op ∈ operations A := by
  intro op hop
  apply List.mem_flatMap.mpr
  exact ⟨A.program pc,List.mem_ofFn.mpr ⟨pc,rfl⟩,hop⟩
 def locate (op : WordOperation A.registers) (h : op ∈ operations A) : Index A :=
  ⟨(operations A).idxOf op,List.idxOf_lt_length_iff.mpr h⟩
 theorem locate_eq (op : WordOperation A.registers) (h : op ∈ operations A) : operation A (locate A op h)=op := by
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr h)
end
end WLTime.RAMAlphabet

namespace WLTime.RAMTests
open TypedStack
open scoped Classical
abbrev Reg := RAMMemory.Reg
def flags (file log : List Bool) (b : Bool) : Stacks Reg Bool :=
  Function.update (RAMMemory.state file log [] []) 11 [b]
def testMap : ZeroTest.Reg → Reg := ![2,11]
theorem testMap_inj : Function.Injective testMap := by decide
noncomputable def testCode (w i : ℕ) : Code Reg Bool :=
  .seq (RAMMemory.readKey w i) (ZeroTest.program.relabel testMap)
 theorem exec {R w : ℕ} (a : Fin R → Word w) (i : Fin R) (log : List Bool) :
    ∃u ≤ 60*(R*w+1)+8*w+10,(testCode w i.val).Exec (RAMMemory.state (registerBits a) log [] []) u
      (flags (registerBits a) log ((wordBits (a i)).any id)) := by
  obtain ⟨t,ht,he⟩ := RAMMemory.readKey_exec a i log []
  have hz := ZeroTest.program_exec (wordBits (a i))
  have hh : (ZeroTest.program.relabel testMap).Exec
      (RAMMemory.state (registerBits a) log (wordBits (a i)) []) (8*w+10)
      (flags (registerBits a) log ((wordBits (a i)).any id)) := by
    have hl : (wordBits (a i)).length=w := by simp [wordBits]
    rw [hl] at hz
    apply Code.relabel_exec_of_maps _ testMap_inj hz
    · intro k; fin_cases k <;> simp [testMap,RAMMemory.state,ZeroTest.state]
    · intro k; fin_cases k <;> simp [testMap,RAMMemory.state,ZeroTest.state,flags]
    · intro k hk; fin_cases k <;> simp_all [testMap,RAMMemory.state,flags,Fin.forall_fin_succ]
  exact ⟨_,by omega,Code.Exec.seq he hh⟩
 theorem pop_exec (file log : List Bool) (b : Bool) :
    (Code.pop 11).Exec (flags file log b) 2 (RAMMemory.state file log [] []) := by
  have he := Code.Exec.pop (flags file log b) 11
  convert he using 1
  funext k; fin_cases k <;> simp [flags,RAMMemory.state]
 theorem code_size (R w : ℕ) (i : Fin R) : (testCode w i.val).controlSize ≤ 10*(R+1)*(w+1)+100 := by
  have he := RAMSlices.read_size (w*i.val) w
  have hi := Nat.mul_le_mul_left w (Nat.le_of_lt i.isLt)
  simp only [testCode,RAMMemory.readKey,Code.controlSize,Code.relabel_controlSize,ZeroTest.program_size]
  nlinarith
end WLTime.RAMTests
namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
 def memCode (c : Code RAMMemory.Reg Bool) : Code (Reg A) (Letter A) :=
  (c.mapLetters Sum.inl (decode A)).relabel (memMap A)
 theorem memCode_size (c : Code RAMMemory.Reg Bool) : (memCode A c).controlSize=c.controlSize := by simp [memCode]
 theorem prefix_exec (pre file log : List Bool) (pc : Fin A.locations) (answer : Option Bool) :
    (Code.pushList (.inl 0) (pre.map (Sum.inl : Bool → Letter A))).Exec (fileState A file log pc answer)
      (2*pre.length+1) (fileState A (pre++file) log pc answer) := by
  have h := Code.pushList_exec (.inl 0 : Reg A) (pre.map (Sum.inl : Bool → Letter A)) (fileState A file log pc answer)
  simp only [List.length_map] at h
  convert h using 1
  funext k
  cases k with
  | inl j => fin_cases j <;> simp [fileState,liftMem,RAMMemory.state]
  | inr j => simp [fileState,liftMem]
 def compute (w : ℕ) (op : WordOperation A.registers) (h : op ∈ operations A) : Code (Reg A) (Letter A) :=
  .seq (.pushList (.inl 0) ((encodeNat w).map Sum.inl))
    (opCode A (locate A op h) ((encodeNat w).length+A.registers*w) (A.registers*w))
 theorem compute_exec {w : ℕ} (op : WordOperation A.registers) (h : op ∈ operations A)
    (C : SparseRAM.Config A.registers A.locations w) :
    ∃u ≤ 2*(encodeNat w).length+1+TMPort.factor op.implementation*
      ((encodeNat w).length+2*(A.registers*w)+op.constant*(w+1)^op.exponent+1),
      (compute A w op h).Exec (state A C) u (state A {C with registers := op.apply w C.registers}) := by
  have hp := prefix_exec A (encodeNat w) (registerBits C.registers)
    (SparseLookup.flatten (WordMemory.entries C.log)) C.pc C.answer
  have ho := op.computes w C.registers
  have he := op_exec A (locate A op h) (encodeNat w++registerBits C.registers)
    (registerBits (op.apply w C.registers)) (SparseLookup.flatten (WordMemory.entries C.log)) C.pc C.answer
  rw [locate_eq] at he
  obtain ⟨u,hu,he⟩ := he ho
  simp only [List.length_append,RegisterFile.length] at hu he
  refine ⟨_,?_,Code.Exec.seq hp he⟩
  have hc := op.cost w C.registers
  exact Nat.add_le_add_left (hu.trans (Nat.mul_le_mul_left _ (by omega))) _
 theorem compute_size (w : ℕ) (op : WordOperation A.registers) (h : op ∈ operations A) :
    (compute A w op h).controlSize ≤ 2*(encodeNat w).length+2+
      TMPort.sizeFactor op.implementation*((encodeNat w).length+2*(A.registers*w)+1) := by
  have he := opCode_size A (locate A op h) ((encodeNat w).length+A.registers*w) (A.registers*w)
  rw [locate_eq] at he
  simp only [compute,Code.controlSize,Code.pushList_size,List.length_map]
  nlinarith only [he]
end
end WLTime.RAMAlphabet

namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
 def opCost (w : ℕ) (op : WordOperation A.registers) : ℕ :=
  2*(encodeNat w).length+1+TMPort.factor op.implementation*
      ((encodeNat w).length+2*(A.registers*w)+op.constant*(w+1)^op.exponent+1)
 def unitCost (w : ℕ) : ℕ := 1000*(A.registers+1)*(w+1)+∑i : Index A,opCost A w (operation A i)
 theorem basic_le_unit (w : ℕ) : 1000*(A.registers+1)*(w+1) ≤ unitCost A w := Nat.le_add_right _ _
 theorem unit_pos (w : ℕ) : 0<unitCost A w := lt_of_lt_of_le (by positivity) (basic_le_unit A w)
 theorem six_le_unit (w : ℕ) : 6≤unitCost A w := (by nlinarith : 6≤1000*(A.registers+1)*(w+1)).trans (basic_le_unit A w)
 theorem op_le_unit (w : ℕ) (op : WordOperation A.registers) (h : op ∈ operations A) : opCost A w op ≤ unitCost A w := by
  have he := Finset.single_le_sum (f:=fun i : Index A => opCost A w (operation A i)) (fun i _ => Nat.zero_le _) (Finset.mem_univ (locate A op h))
  rw [locate_eq] at he
  exact he.trans (Nat.le_add_left _ _)
 theorem memory_le_unit (w L : ℕ) : RAMMemory.cost A.registers w L ≤ unitCost A w*(L+1) := by
  have he := Nat.mul_le_mul_right (L+1) (basic_le_unit A w)
  unfold RAMMemory.cost
  nlinarith only [he]
 theorem test_le_unit (w : ℕ) : 60*(A.registers*w+1)+8*w+13 ≤ unitCost A w := by
  exact (by nlinarith : 60*(A.registers*w+1)+8*w+13≤1000*(A.registers+1)*(w+1)).trans (basic_le_unit A w)
 def haltCode (b : Bool) : Code (Reg A) (Letter A) := .seq (.clear (.inl 13)) (.push (.inl 13) (.inl b))
 def jumpCode (pc : Fin A.locations) : Code (Reg A) (Letter A) := .seq (.clear (.inl 12)) (.push (.inl 12) (.inr (.inl pc)))
 theorem halt_exec {w : ℕ} (C : SparseRAM.Config A.registers A.locations w) (b : Bool) :
    ∃u ≤ 6,(haltCode A b).Exec (state A C) u (state A {C with answer := some b}) := by
  have hc := Code.clear_exec (.inl 13 : Reg A) (state A C)
  have hp := Code.Exec.push (Function.update (state A C) (.inl 13) []) (.inl 13) (.inl b)
  have he := Code.Exec.seq hc hp
  have hout : Function.update (Function.update (state A C) (.inl 13) []) (.inl 13)
      (Sum.inl b::(Function.update (state A C) (.inl 13) []) (.inl 13))=state A {C with answer := some b} := by
    funext k
    cases k with
    | inl j => fin_cases j <;> simp [state,liftMem]
    | inr j => simp [state,liftMem]
  rw [hout] at he
  refine ⟨_,?_,he⟩
  cases C.answer <;> simp [state,liftMem]
 theorem jump_exec {w : ℕ} (C : SparseRAM.Config A.registers A.locations w) (pc : Fin A.locations) :
    (jumpCode A pc).Exec (state A C) 6 (state A {C with pc := pc}) := by
  have hc := Code.clear_exec (.inl 12 : Reg A) (state A C)
  have hp := Code.Exec.push (Function.update (state A C) (.inl 12) []) (.inl 12) (.inr (.inl pc))
  have he := Code.Exec.seq hc hp
  convert he using 1
  · rfl
  · simp [state,liftMem]
  · funext k
    cases k with
    | inl j => fin_cases j <;> simp [state,liftMem]
    | inr j => simp [state,liftMem]
 theorem test_tops (file log : List Bool) (b : Bool) (pc : Fin A.locations) (answer : Option Bool) :
    ((tops (liftMem A (RAMTests.flags file log b) pc answer) (.inl 11)).map (decode A)).getD false=b := by
  simp [tops,liftMem,RAMTests.flags,decode]
 theorem combine_cost (B L D a b : ℕ) (ha : a≤ B*(L+1)) (hb : b≤B*D*(L+D+2)) :
    a+b≤B*(D+1)*(L+(D+1)+1) := by
  have hh : B*(L+1)≤B*(L+D+2) := Nat.mul_le_mul_left _ (by omega)
  calc
    a+b≤B*(L+D+2)+B*D*(L+D+2) := Nat.add_le_add (ha.trans hh) hb
    _=B*(D+1)*(L+(D+1)+1) := by ring
end
end WLTime.RAMAlphabet

end OAI
