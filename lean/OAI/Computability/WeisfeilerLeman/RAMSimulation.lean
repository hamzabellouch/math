import OAI.Computability.WeisfeilerLeman.RAMInstruction

namespace OAI

universe uK uX uT

namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
def instruction (w : ℕ) : (I : RAMInstruction A.registers A.locations) →
    (∀op ∈ I.operations,op ∈ operations A) → Code (Reg A) (Letter A)
  | .halt b,_ => haltCode A b
  | .jump pc,_ => jumpCode A pc
  | .compute op next,h => .seq (compute A w op (h op (by simp [RAMInstruction.operations])))
      (instruction w next (fun q hq => h q (by simp [RAMInstruction.operations,hq])))
  | .load dest addr next,h => .seq (memCode A (RAMMemory.load w dest.val addr.val))
      (instruction w next h)
  | .store addr src next,h => .seq (memCode A (RAMMemory.save w addr.val src.val))
      (instruction w next h)
  | .branchZero reg yes no,h =>
      .seq (memCode A (RAMTests.testCode w reg.val))
        (.branch (fun v => ((v (.inl 11)).map (decode A)).getD false)
          (.seq (.pop (.inl 11)) (instruction w no (fun q hq => h q (by simp [RAMInstruction.operations,hq]))))
          (.seq (.pop (.inl 11)) (instruction w yes (fun q hq => h q (by simp [RAMInstruction.operations,hq])))))
 theorem bound_mono (B L D E : ℕ) (h : D≤E) : B*D*(L+D+1)≤B*E*(L+E+2) :=
  Nat.mul_le_mul (Nat.mul_le_mul_left _ h) (by omega)
 theorem instruction_exec {w : ℕ} (hw : 0<w) (I : RAMInstruction A.registers A.locations)
    (h : ∀op ∈ I.operations,op ∈ operations A) (C : SparseRAM.Config A.registers A.locations w) :
    ∃u ≤ unitCost A w*I.depth*(C.log.length+I.depth+1),
      (instruction A w I h).Exec (state A C) u (state A (SparseRAM.execute I C)) := by
  induction I generalizing C with
  | halt b =>
    obtain ⟨u,hu,he⟩ := halt_exec A C b
    refine ⟨u,?_,he⟩
    exact (hu.trans (six_le_unit A w)).trans (by simp only [RAMInstruction.depth,Nat.mul_one]; exact Nat.le_mul_of_pos_right _ (by omega))
  | jump pc =>
    refine ⟨6,?_,jump_exec A C pc⟩
    exact (six_le_unit A w).trans (by simp only [RAMInstruction.depth,Nat.mul_one]; exact Nat.le_mul_of_pos_right _ (by omega))
  | compute op next ih =>
    let hn : ∀q ∈ next.operations,q ∈ operations A := fun q hq => h q (by simp [RAMInstruction.operations,hq])
    let hop : op ∈ operations A := h op (by simp [RAMInstruction.operations])
    obtain ⟨x,hx,he⟩ := compute_exec A op hop C
    obtain ⟨y,hy,hf⟩ := ih hn {C with registers := op.apply w C.registers}
    refine ⟨x+y,?_,Code.Exec.seq he hf⟩
    apply combine_cost
    · exact (hx.trans (op_le_unit A w op hop)).trans (Nat.le_mul_of_pos_right _ (by omega))
    · exact hy.trans (bound_mono _ _ _ _ le_rfl)
  | load dest addr next ih =>
    obtain ⟨x,hx,he⟩ := RAMMemory.load_exec hw C.registers C.log dest addr
    have hh := mem_exec A he C.pc C.answer
    obtain ⟨y,hy,hf⟩ := ih h {C with registers := Function.update C.registers dest (WordMemory.read (C.registers addr) C.log)}
    refine ⟨x+y,?_,Code.Exec.seq hh hf⟩
    apply combine_cost
    · exact hx.trans (memory_le_unit A w C.log.length)
    · exact hy.trans (bound_mono _ _ _ _ le_rfl)
  | store addr src next ih =>
    obtain ⟨x,hx,he⟩ := RAMMemory.save_exec C.registers C.log addr src
    have hh := mem_exec A he C.pc C.answer
    obtain ⟨y,hy,hf⟩ := ih h {C with log := (C.registers addr,C.registers src)::C.log}
    refine ⟨x+y,?_,Code.Exec.seq hh hf⟩
    apply combine_cost
    · exact hx.trans ((memory_le_unit A w 0).trans (by simpa using Nat.le_mul_of_pos_right (unitCost A w) (by omega : 0<C.log.length+1)))
    · change y≤unitCost A w*next.depth*(C.log.length+1+next.depth+1) at hy
      convert hy using 1
      congr 1
      omega
  | branchZero reg yes no ih ih' =>
    let hy : ∀q ∈ yes.operations,q ∈ operations A := fun q hq => h q (by simp [RAMInstruction.operations,hq])
    let hn : ∀q ∈ no.operations,q ∈ operations A := fun q hq => h q (by simp [RAMInstruction.operations,hq])
    obtain ⟨x,hx,he⟩ := RAMTests.exec C.registers reg (SparseLookup.flatten (WordMemory.entries C.log))
    have hh := mem_exec A he C.pc C.answer
    have hp := mem_exec A (RAMTests.pop_exec (registerBits C.registers)
      (SparseLookup.flatten (WordMemory.entries C.log)) ((wordBits (C.registers reg)).any id)) C.pc C.answer
    have htest := test_tops A (registerBits C.registers) (SparseLookup.flatten (WordMemory.entries C.log))
      ((wordBits (C.registers reg)).any id) C.pc C.answer
    have hx' : x+3≤unitCost A w*(C.log.length+1) :=
      (show x+3≤unitCost A w from (by have ht := test_le_unit A w; omega)).trans (Nat.le_mul_of_pos_right _ (by omega))
    by_cases hz : (C.registers reg).val=0
    · have hb := (ZeroTest.word_zero_iff (C.registers reg)).mpr hz
      have ht := htest.trans hb
      obtain ⟨y,hy',hf⟩ := ih hy C
      have hc := Code.Exec.seq hh (Code.Exec.branch_false
        (a:=.seq (.pop (.inl 11)) (instruction A w no hn)) (p:=fun v : Tops (Reg A) (Letter A) => ((v (.inl 11)).map (decode A)).getD false) ht (Code.Exec.seq hp hf))
      refine ⟨x+(1+(2+y)),?_,?_⟩
      · have hy'' := hy'.trans (bound_mono (unitCost A w) C.log.length yes.depth (max yes.depth no.depth) (le_max_left _ _))
        have hbound := combine_cost (unitCost A w) C.log.length (max yes.depth no.depth) (x+3) y hx' hy''
        simpa only [RAMInstruction.depth,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hbound
      · convert hc using 1
        all_goals try rfl
        · omega
        · simp only [SparseRAM.execute,ite_eq_left hz]
    · have hb : (wordBits (C.registers reg)).any id=true := by
        cases hb : (wordBits (C.registers reg)).any id
        · exact False.elim (hz ((ZeroTest.word_zero_iff _).mp hb))
        · rfl
      have ht := htest.trans hb
      obtain ⟨y,hy',hf⟩ := ih' hn C
      have hc := Code.Exec.seq hh (Code.Exec.branch_true
        (b:=.seq (.pop (.inl 11)) (instruction A w yes hy)) (p:=fun v : Tops (Reg A) (Letter A) => ((v (.inl 11)).map (decode A)).getD false) ht (Code.Exec.seq hp hf))
      refine ⟨x+(1+(2+y)),?_,?_⟩
      · have hy'' := hy'.trans (bound_mono (unitCost A w) C.log.length no.depth (max yes.depth no.depth) (le_max_right _ _))
        have hbound := combine_cost (unitCost A w) C.log.length (max yes.depth no.depth) (x+3) y hx' hy''
        simpa only [RAMInstruction.depth,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hbound
      · convert hc using 1
        all_goals try rfl
        · omega
        · simp only [SparseRAM.execute,ite_eq_right hz]
end
end WLTime.RAMAlphabet

namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
 theorem encode_length_bound (w : ℕ) : (encodeNat w).length ≤ 2*w+1 := by
  have hd : (Nat.digits 2 w).length≤w := (Nat.digits_length_le_iff (by decide) w).mpr w.lt_two_pow_self
  simp only [encodeNat,List.length_append,List.length_replicate,List.length_cons,List.length_nil,List.length_map]
  omega
 def exponent : ℕ := 1+Finset.univ.sup (fun i : Index A => (operation A i).exponent)
 def opConstant (op : WordOperation A.registers) : ℕ :=
  7+TMPort.factor op.implementation*(2*A.registers+op.constant+4)
 def constant : ℕ := 1000*(A.registers+1)+∑i : Index A,opConstant A (operation A i)
 theorem opCost_bound (w : ℕ) (op : WordOperation A.registers) :
    opCost A w op ≤ opConstant A op*(w+1)^(op.exponent+1) := by
  have hl := encode_length_bound w
  have hp : w+1≤(w+1)^(op.exponent+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<w+1) (by omega : 1≤op.exponent+1)
  have hq : (w+1)^op.exponent≤(w+1)^(op.exponent+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hr : 2*(A.registers*w)≤2*A.registers*((w+1)^(op.exponent+1)) := by
    calc
      _=2*A.registers*w := by ring
      _≤_ := Nat.mul_le_mul_left _ (by omega)
  have hc := Nat.mul_le_mul_left op.constant hq
  have hin : (encodeNat w).length+2*(A.registers*w)+op.constant*(w+1)^op.exponent+1≤
      (2*A.registers+op.constant+4)*(w+1)^(op.exponent+1) := by nlinarith only [hl,hp,hr,hc]
  have hh := Nat.mul_le_mul_left (TMPort.factor op.implementation) hin
  dsimp only [opCost,opConstant]
  nlinarith only [hl,hp,hh]
 theorem unitCost_bound (w : ℕ) : unitCost A w ≤ constant A*(w+1)^exponent A := by
  have he : 1≤exponent A := by unfold exponent; omega
  have hw : w+1≤(w+1)^exponent A := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<w+1) he
  have hs : (∑i : Index A,opCost A w (operation A i)) ≤
      (∑i : Index A,opConstant A (operation A i))*(w+1)^exponent A := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hi : (operation A i).exponent+1≤exponent A := by
      have hh := Finset.le_sup (f:=fun i : Index A => (operation A i).exponent) (Finset.mem_univ i)
      unfold exponent; omega
    exact (opCost_bound A w (operation A i)).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hi))
  have hb := Nat.mul_le_mul_left (1000*(A.registers+1)) hw
  dsimp only [unitCost,constant]
  nlinarith only [hs,hb]
 def opSizeConstant (op : WordOperation A.registers) : ℕ := 10+TMPort.sizeFactor op.implementation*(2*A.registers+4)
 theorem compute_linear (w : ℕ) (op : WordOperation A.registers) (h : op ∈ operations A) :
    (compute A w op h).controlSize ≤ opSizeConstant A op*(w+1) := by
  have he := compute_size A w op h
  have hl := encode_length_bound w
  have hh := Nat.mul_le_mul_left (TMPort.sizeFactor op.implementation)
    (show (encodeNat w).length+2*(A.registers*w)+1≤(2*A.registers+4)*(w+1) by nlinarith only [hl])
  dsimp only [opSizeConstant]
  nlinarith only [he,hl,hh]
 theorem instruction_linear (I : RAMInstruction A.registers A.locations) :
    ∃S,∀w h,(instruction A w I h).controlSize≤S*(w+1) := by
  induction I with
  | halt b =>
    refine ⟨10,?_⟩
    intro w h
    simp only [instruction,haltCode,Code.controlSize,Code.clear]
    omega
  | jump pc =>
    refine ⟨10,?_⟩
    intro w h
    simp only [instruction,jumpCode,Code.controlSize,Code.clear]
    omega
  | compute op next ih =>
    obtain ⟨S,hS⟩ := ih
    refine ⟨opSizeConstant A op+S+1,?_⟩
    intro w h
    have hn : ∀q∈next.operations,q∈operations A := fun q hq => h q (by simp [RAMInstruction.operations,hq])
    have ho := compute_linear A w op (h op (by simp [RAMInstruction.operations]))
    have hs := hS w hn
    simp only [instruction,Code.controlSize]
    nlinarith only [ho,hs]
  | load dest addr next ih =>
    obtain ⟨S,hS⟩ := ih
    refine ⟨500*(A.registers+1)+S+1,?_⟩
    intro w h
    have hm := RAMMemory.load_size A.registers w dest addr
    have hs := hS w h
    simp only [instruction,Code.controlSize,memCode_size]
    simp only [RAMMemory.cost,Nat.zero_add,Nat.mul_one] at hm
    nlinarith only [hm,hs]
  | store addr src next ih =>
    obtain ⟨S,hS⟩ := ih
    refine ⟨500*(A.registers+1)+S+1,?_⟩
    intro w h
    have hm := RAMMemory.save_size A.registers w addr src
    have hs := hS w h
    simp only [instruction,Code.controlSize,memCode_size]
    simp only [RAMMemory.cost,Nat.zero_add,Nat.mul_one] at hm
    nlinarith only [hm,hs]
  | branchZero reg yes no ih ih' =>
    obtain ⟨S,hS⟩ := ih
    obtain ⟨T,hT⟩ := ih'
    refine ⟨110*(A.registers+1)+S+T+10,?_⟩
    intro w h
    have hy : ∀q∈yes.operations,q∈operations A := fun q hq => h q (by simp [RAMInstruction.operations,hq])
    have hn : ∀q∈no.operations,q∈operations A := fun q hq => h q (by simp [RAMInstruction.operations,hq])
    have hs := hS w hy
    have ht := hT w hn
    have hm := RAMTests.code_size A.registers w reg
    simp only [instruction,Code.controlSize,memCode_size]
    nlinarith only [hs,ht,hm]
end
end WLTime.RAMAlphabet

namespace WLTime.TypedStack.Code
variable {K : Type uK} {X : Type uX} {T : Type uT} [DecidableEq K] [DecidableEq T]
 omit [DecidableEq K] in
 theorem casesList_size (select : Tops K X → T) (body : T → Code K X) (xs : List T) :
    (casesList select body xs).controlSize=1+xs.length+(xs.map (fun x => (body x).controlSize)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [casesList,controlSize,ih,List.length_cons,List.map_cons,List.sum_cons]; omega
 omit [DecidableEq K] in
 theorem casesAll_size [Fintype T] (select : Tops K X → T) (body : T → Code K X) :
    (casesAll select body).controlSize=1+Fintype.card T+∑x : T,(body x).controlSize := by
  rw [casesAll,casesList_size,Finset.length_toList,Finset.card_univ]
  congr 1
  exact Finset.sum_map_toList _ _
end WLTime.TypedStack.Code
namespace WLTime.SparseRAM
 theorem iterate_fixed (A : RAM) (w : ℕ) (C : Config A.registers A.locations w) (h : C.answer.isSome=true) (t : ℕ) :
    (step A w)^[t] C=C := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,step_fixed A w C h]
end WLTime.SparseRAM
namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
def depth : ℕ := Finset.univ.sup (fun pc : Fin A.locations => (A.program pc).depth)
theorem depth_le (pc : Fin A.locations) : (A.program pc).depth≤depth A := Finset.le_sup (f:=fun pc : Fin A.locations => (A.program pc).depth) (Finset.mem_univ pc)
theorem depth_pos : 0<depth A := (A.program ⟨0,A.locations_pos⟩).depth_pos.trans_le (depth_le A _)
def selectPC (v : Tops (Reg A) (Letter A)) : Fin A.locations :=
  match v (.inl 12) with
  | some (.inr (.inl pc)) => pc
  | _ => ⟨0,A.locations_pos⟩
def dispatch (w : ℕ) : Code (Reg A) (Letter A) :=
  Code.casesAll (selectPC A) (fun pc : Fin A.locations => instruction A w (A.program pc) (mem_program A pc))
def stepBound (w L : ℕ) : ℕ := unitCost A w*depth A*(L+depth A+1)+A.locations
theorem stepBound_mono (w L L' : ℕ) (h : L≤L') : stepBound A w L ≤ stepBound A w L' := by
  unfold stepBound
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
theorem select_state {w : ℕ} (C : SparseRAM.Config A.registers A.locations w) : selectPC A (tops (state A C))=C.pc := by
  simp [selectPC,tops,state,liftMem]
 theorem dispatch_exec {w : ℕ} (hw : 0<w) (C : SparseRAM.Config A.registers A.locations w) :
    ∃u ≤ stepBound A w C.log.length,(dispatch A w).Exec (state A C) u (state A (SparseRAM.execute (A.program C.pc) C)) := by
  obtain ⟨t,ht,he⟩ := instruction_exec A hw (A.program C.pc) (mem_program A C.pc) C
  have hh : ((fun pc : Fin A.locations => instruction A w (A.program pc) (mem_program A pc)) (selectPC A (tops (state A C)))).Exec
      (state A C) t (state A (SparseRAM.execute (A.program C.pc) C)) := by simpa only [select_state] using he
  obtain ⟨u,hu,hg⟩ := Code.casesAll_exec (selectPC A) (fun pc : Fin A.locations => instruction A w (A.program pc) (mem_program A pc)) hh
  refine ⟨u,?_,hg⟩
  simp only [Fintype.card_fin] at hu
  have hd := depth_le A C.pc
  have hb : t≤unitCost A w*depth A*(C.log.length+depth A+1) := ht.trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ hd) (by omega))
  unfold stepBound
  omega
 def running (v : Tops (Reg A) (Letter A)) : Bool := !(v (.inl 13)).isSome
 def loopCode (w : ℕ) : Code (Reg A) (Letter A) := .loop (running A) (dispatch A w)
 theorem running_state {w : ℕ} (C : SparseRAM.Config A.registers A.locations w) :
    running A (tops (state A C)) = !C.answer.isSome := by
  cases h : C.answer <;> simp [running,tops,state,liftMem,h]
 theorem loop_exec {w : ℕ} (hw : 0<w) (t : ℕ) (C : SparseRAM.Config A.registers A.locations w)
    (hend : ((SparseRAM.step A w)^[t] C).answer.isSome=true) :
    ∃u ≤ (stepBound A w (C.log.length+t*depth A)+1)*t+1,
      (loopCode A w).Exec (state A C) u (state A ((SparseRAM.step A w)^[t] C)) := by
  induction t generalizing C with
  | zero =>
    simp only [Function.iterate_zero, id_eq] at hend ⊢
    refine ⟨1,by simp,?_⟩
    apply Code.Exec.loop_false
    simpa only [running_state,hend] using (show (!true)=false by rfl)
  | succ t ih =>
    cases ha : C.answer with
    | some b =>
      have hc : C.answer.isSome=true := by rw [ha]; rfl
      have hf := SparseRAM.iterate_fixed A w C hc (t+1)
      rw [hf]
      refine ⟨1,by omega,Code.Exec.loop_false ?_⟩
      simp only [running_state,hc,Bool.not_true]
    | none =>
      let C' := SparseRAM.execute (A.program C.pc) C
      have hs : SparseRAM.step A w C=C' := by simp [SparseRAM.step,ha,C']
      have hend' : ((SparseRAM.step A w)^[t] C').answer.isSome=true := by
        simpa only [Function.iterate_succ_apply,hs] using hend
      obtain ⟨x,hx,he⟩ := dispatch_exec A hw C
      obtain ⟨y,hy,hf⟩ := ih C' hend'
      have hl : C'.log.length≤C.log.length+depth A :=
        (SparseRAM.execute_log_length (A.program C.pc) C).trans (Nat.add_le_add_left (depth_le A C.pc) _)
      have hb := stepBound_mono A w C.log.length (C.log.length+(t+1)*depth A) (by omega)
      have hh := stepBound_mono A w (C'.log.length+t*depth A) (C.log.length+(t+1)*depth A) (by nlinarith only [hl])
      refine ⟨x+y+1,?_,?_⟩
      · have hh' := Nat.mul_le_mul_right t (Nat.add_le_add_right hh 1)
        nlinarith only [hx,hy,hb,hh']
      · have hg := Code.Exec.loop_true (p:=running A) (by simp only [running_state,ha,Option.isSome_none,Bool.not_false]) he hf
        simpa only [loopCode,Function.iterate_succ_apply,hs] using hg
 theorem dispatch_linear : ∃S,∀w,(dispatch A w).controlSize≤S*(w+1) := by
  choose S hS using fun pc : Fin A.locations => instruction_linear A (A.program pc)
  refine ⟨1+A.locations+∑pc,S pc,?_⟩
  intro w
  have hs : (∑pc : Fin A.locations,(instruction A w (A.program pc) (mem_program A pc)).controlSize)≤(∑pc,S pc)*(w+1) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun pc _ => hS pc w (mem_program A pc))
  rw [dispatch,Code.casesAll_size,Fintype.card_fin]
  nlinarith only [hs]
end
end WLTime.RAMAlphabet

namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
def inputMap (i : RAMInput.Reg) : RAMMemory.Reg := ⟨i.val,by omega⟩
theorem inputMap_inj : Function.Injective inputMap := by
  intro i j h
  exact Fin.ext (Fin.mk.inj h)
def loader (w : ℕ) : Code RAMMemory.Reg Bool := (RAMInput.program w).relabel inputMap
 theorem loader_exec (w : ℕ) (hw : 0<w) (input : List Bool) (hfit : input.length≤w*2^w) :
    ∃n ≤ input.length, (fun q => WordMemory.read q (WordMemory.initialLog w input n))=RAM.packedWord w input ∧
      ∃u ≤60*(w+1)*(input.length+1),(loader w).Exec (RAMMemory.state input [] [] []) u
        (RAMMemory.state [] (SparseLookup.flatten (WordMemory.entries (WordMemory.initialLog w input n))) [] []) := by
  obtain ⟨n,hn,hm,u,hu,he⟩ := RAMInput.program_exec w hw input hfit
  refine ⟨n,hn,hm,u,hu,?_⟩
  apply Code.relabel_exec_of_maps _ inputMap_inj he
  · intro i; fin_cases i <;> simp [inputMap,RAMMemory.state,RAMInput.state]
  · intro i; fin_cases i <;> simp [inputMap,RAMMemory.state,RAMInput.state]
  · intro i hi; fin_cases i <;> simp_all [inputMap,RAMMemory.state,Fin.forall_fin_succ]
 def inputState (xs : List Bool) : Stacks (Reg A) (Letter A) := fun r => if r=.inl 0 then xs.map Sum.inl else []
 def initial (w : ℕ) (xs : List Bool) (n : ℕ) : SparseRAM.Config A.registers A.locations w where
  pc := ⟨0,A.locations_pos⟩
  registers := fun _ => ⟨0,by positivity⟩
  log := WordMemory.initialLog w xs n
  answer := none
 def initCode (w : ℕ) : Code (Reg A) (Letter A) :=
  .seq (.push (.inl 12) (.inr (.inl ⟨0,A.locations_pos⟩)))
    (.seq (memCode A (loader w)) (.pushList (.inl 0) ((List.replicate (A.registers*w) false).map Sum.inl)))
 def initBound (w len : ℕ) : ℕ := 100*(A.registers+1)*(w+1)*(len+1)
 theorem init_exec (w : ℕ) (hw : 0<w) (input : List Bool) (hfit : input.length≤w*2^w) :
    ∃n ≤ input.length, (fun q => WordMemory.read q (WordMemory.initialLog w input n))=RAM.packedWord w input ∧
      ∃u ≤ initBound A w input.length,(initCode A w).Exec (inputState A input) u (state A (initial A w input n)) := by
  obtain ⟨n,hn,hm,t,ht,he⟩ := loader_exec w hw input hfit
  have hp : (Code.push (.inl 12) (.inr (.inl ⟨0,A.locations_pos⟩))).Exec (inputState A input) 2
      (fileState A input [] ⟨0,A.locations_pos⟩ none) := by
    have hh := Code.Exec.push (inputState A input) (.inl 12) (.inr (.inl ⟨0,A.locations_pos⟩))
    convert hh using 1
    funext r
    cases r with
    | inl i => fin_cases i <;> simp [inputState,fileState,liftMem,RAMMemory.state]
    | inr r => simp [inputState,fileState,liftMem]
  have hh := mem_exec A he ⟨0,A.locations_pos⟩ none
  have hg := prefix_exec A (List.replicate (A.registers*w) false) []
    (SparseLookup.flatten (WordMemory.entries (WordMemory.initialLog w input n))) ⟨0,A.locations_pos⟩ none
  have hout : fileState A (List.replicate (A.registers*w) false++[]) (SparseLookup.flatten (WordMemory.entries (WordMemory.initialLog w input n))) ⟨0,A.locations_pos⟩ none=state A (initial A w input n) := by
    simp only [List.append_nil,state,fileState,initial,RegisterFile.zero]
  rw [hout,List.length_replicate] at hg
  refine ⟨n,hn,hm,_,?_,Code.Exec.seq hp (Code.Exec.seq hh hg)⟩
  have h₁ : (w+1)*(input.length+1)≤(A.registers+1)*(w+1)*(input.length+1) :=
    Nat.mul_le_mul_right _ (by nlinarith)
  have h₂ : A.registers*w≤(A.registers+1)*(w+1)*(input.length+1) := by
    exact (by nlinarith : A.registers*w≤(A.registers+1)*(w+1)).trans (Nat.le_mul_of_pos_right _ (by omega))
  have h₃ : 1≤(A.registers+1)*(w+1)*(input.length+1) := by
    have : 0<(A.registers+1)*(w+1)*(input.length+1) := by positivity
    omega
  unfold initBound
  nlinarith only [ht,h₁,h₂,h₃]
 theorem initial_forget (n : ℕ) (input : List Bool) (chunks : ℕ)
    (hm : (fun q => WordMemory.read q (WordMemory.initialLog (A.width.bits n) input chunks))=RAM.packedWord (A.width.bits n) input) :
    SparseRAM.forget A n (initial A (A.width.bits n) input chunks)=A.initial n input := by
  unfold SparseRAM.forget initial RAM.initial
  congr 1
 def program (w : ℕ) : Code (Reg A) (Letter A) := .seq (initCode A w) (loopCode A w)
 def budget (w len time : ℕ) : ℕ := initBound A w len+(stepBound A w (len+time*depth A)+1)*time+1
 theorem program_exec (n : ℕ) (input : List Bool) (hfit : input.length≤A.width.bits n*2^(A.width.bits n)) (hh : A.halts n input) :
    ∃u ≤ budget A (A.width.bits n) input.length (A.time n input),∃b out,
      (program A (A.width.bits n)).Exec (inputState A input) u out ∧
      out (.inl 13)=[.inl b] ∧ (b=true ↔ A.accepts n input) := by
  obtain ⟨chunks,hchunks,hm,t,ht,he⟩ := init_exec A (A.width.bits n) (A.width.positive n) input hfit
  let C := initial A (A.width.bits n) input chunks
  let T := A.time n input
  let out := (SparseRAM.step A (A.width.bits n))^[T] C
  have hforget : A.run n input T=SparseRAM.forget A n out := by
    rw [RAM.run,←initial_forget A n input chunks hm]
    exact SparseRAM.iterate_forget A n C T
  have hend : out.answer.isSome=true := by
    have h := A.time_halted n input hh
    rw [hforget] at h
    exact h
  obtain ⟨s,hs,hf⟩ := loop_exec A (A.width.positive n) T C hend
  have hl : C.log.length=chunks := WordMemory.initialLog_length _ _ _
  rw [hl] at hs
  obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp hend
  refine ⟨t+s,?_,b,state A out,Code.Exec.seq he hf,?_,?_⟩
  · have hm' := stepBound_mono A (A.width.bits n) (chunks+T*depth A) (input.length+T*depth A) (by omega)
    have hx := Nat.mul_le_mul_right T (Nat.add_le_add_right hm' 1)
    unfold budget
    dsimp only [T] at *
    omega
  · simp [state,liftMem,hb]
  · have ha : (A.run n input T).answer=some b := by rw [hforget]; exact hb
    exact (A.accepts_iff_answer n input T b ha).symm
 theorem init_linear (w : ℕ) : (initCode A w).controlSize≤500*(A.registers+1)*(w+1) := by
  have he := RAMInput.program_size w
  simp only [initCode,Code.controlSize,memCode_size,loader,Code.relabel_controlSize,Code.pushList_size,List.length_map,List.length_replicate]
  nlinarith only [he]
 theorem program_linear : ∃S,∀w,(program A w).controlSize≤S*(w+1) := by
  obtain ⟨S,hS⟩ := dispatch_linear A
  refine ⟨500*(A.registers+1)+S+1,?_⟩
  intro w
  have hi := init_linear A w
  have hd := hS w
  simp only [program,loopCode,Code.controlSize]
  nlinarith only [hi,hd]
end
end WLTime.RAMAlphabet

end OAI
