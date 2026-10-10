import Mathlib
import OAI.Probability.Contingency.StackSequence

namespace OAI

/-! Parse Nat Runs. -/

noncomputable section


namespace Contingency.BitModel.StackCode.ParseNat
noncomputable section

theorem data_done (m : Memory 4) (h2 : m.stack 2=[]) :
    exec 1 (config .data m)=config .restore (m.pop 2) := by
  rw [exec_one,one_step]
  simp [code,effect,branch,h2,config]; rfl

theorem restore_empty (m : Memory 4) (h1 : m.stack 1=[]) :
    exec 1 (config .restore m)=config .done (m.pop 1) := by
  rw [exec_one,one_step]
  simp [code,effect,branch,h1,config]; rfl

theorem restore_bit (m : Memory 4) (b : Bool) (bs : List Bool) (h1 : m.stack 1=b::bs) :
    exec 2 (config .restore m)=config .restore ((m.pop 1).push 0 b) := by
  change step program false (step program false (config .restore m))=_
  rw [one_step]
  have he : (⟨(effect (code .restore) false m).1,(effect (code .restore) false m).2⟩ : Config program)=config (.place b) (m.pop 1) := by
    cases b <;> simp [code,effect,branch,h1,config] <;> rfl
  rw [he,one_step]; rfl

def restoreMemory : List Bool→Memory 4→Memory 4
  | [],m => m.pop 1
  | b::bs,m => restoreMemory bs ((m.pop 1).push 0 b)

theorem restore_run (bs : List Bool) (m : Memory 4) (h1 : m.stack 1=bs) :
    exec (2*bs.length+1) (config .restore m)=config .done (restoreMemory bs m) := by
  induction bs generalizing m with
  | nil => exact restore_empty m h1
  | cons b bs ih =>
    have he : 2*(b::bs).length+1=2+(2*bs.length+1) := by simp; omega
    rw [he,exec_add,restore_bit m b bs h1,ih]
    · rfl
    · simp [Memory.push,Memory.pop,h1]

theorem restoreMemory_fields (bs : List Bool) (m : Memory 4) (h1 : m.stack 1=bs) :
    (restoreMemory bs m).input=m.input ∧
    (restoreMemory bs m).stack 0=bs.reverse++m.stack 0 ∧
    (restoreMemory bs m).stack 1=[] ∧
    (restoreMemory bs m).stack 2=m.stack 2 ∧
    (restoreMemory bs m).stack 3=m.stack 3 ∧
    (restoreMemory bs m).outputRev=m.outputRev := by
  induction bs generalizing m with
  | nil => simp [restoreMemory,Memory.pop,h1]
  | cons b bs ih =>
    have hh := ih ((m.pop 1).push 0 b) (by simp [Memory.pop,Memory.push,h1])
    simpa [restoreMemory,Memory.pop,Memory.push,List.reverse_cons,List.append_assoc] using hh

theorem halt (m : Memory 4) : exec 1 (config .done m)=⟨none,m⟩ := by
  rw [exec_one,one_step]; rfl

 

theorem parse_word (bs : List Bool) (m : Memory 4) (rest : List Bool)
    (hi : m.input=List.replicate bs.length true++false::(bs++rest))
    (h1 : m.stack 1=[]) (h2 : m.stack 2=[]) :
    ∃ m' : Memory 4,exec (7*bs.length+4) (config .prefix m)=⟨none,m'⟩ ∧
      m'.input=rest ∧ m'.stack 0=bs++m.stack 0 ∧
      m'.stack 1=[] ∧ m'.stack 2=[] ∧ m'.stack 3=m.stack 3 ∧ m'.outputRev=m.outputRev := by
  let p := prefixMemory bs.length m
  have hp := prefixMemory_fields bs.length m (bs++rest) hi
  have hp2 : p.stack 2=List.replicate bs.length false := by simpa [p,h2] using hp.2.2.2.1
  let d := dataMemory bs p
  have hd := dataMemory_fields bs p rest hp.1 hp2
  have hd1 : (d.pop 2).stack 1=bs.reverse := by
    simpa [d,Memory.pop,p,hp.2.2.1,h1] using hd.2.2.1
  let r := restoreMemory bs.reverse (d.pop 2)
  have hr := restoreMemory_fields bs.reverse (d.pop 2) hd1
  refine ⟨r,?_,?_,?_,hr.2.2.1,?_,?_,?_⟩
  · have he : 7*bs.length+4=(((2*bs.length+1)+3*bs.length)+1)+(2*bs.reverse.length+1)+1 := by simp; omega
    rw [he,exec_add _ 1,exec_add (((2*bs.length+1)+3*bs.length)+1) (2*bs.reverse.length+1),exec_add ((2*bs.length+1)+3*bs.length) 1,exec_add (2*bs.length+1) (3*bs.length)]
    rw [prefix_run bs.length m (bs++rest) hi,data_run bs p rest hp.1 hp2,data_done _ hd.2.2.2.1,restore_run bs.reverse (d.pop 2) hd1,halt]
  · exact hr.1.trans hd.1
  · calc
      r.stack 0=bs.reverse.reverse++(d.pop 2).stack 0 := hr.2.1
      _ = bs++m.stack 0 := by
        simp only [List.reverse_reverse]
        congr 1
        simpa [Memory.pop] using hd.2.1.trans hp.2.1
  · have hd2 : d.stack 2=[] := hd.2.2.2.1
    exact hr.2.2.2.1.trans (by simp [Memory.pop,hd2])
  · exact hr.2.2.2.2.1.trans (hd.2.2.2.2.1.trans hp.2.2.2.2.1)
  · exact hr.2.2.2.2.2.trans (hd.2.2.2.2.2.trans hp.2.2.2.2.2)

theorem step_independent (cfg : Config program) (b b' : Bool) :
    step program b cfg=step program b' cfg := by
  rcases cfg with ⟨s,m⟩
  cases s with
  | none => rfl
  | some pc =>
    unfold step
    dsimp only [program]
    cases (Fintype.equivFin Q).symm pc <;> rfl

theorem fold_independent (xs ys : List Bool) (hl : xs.length=ys.length) (cfg : Config program) :
    xs.foldl (fun cfg b => step program b cfg) cfg=ys.foldl (fun cfg b => step program b cfg) cfg := by
  induction xs generalizing ys cfg with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hl
      simp only [List.foldl_cons]
      rw [step_independent _ x y]
      exact ih _ hl _

 

theorem parse_nat_tape (x : ℕ) (rest : List Bool) :
    ∃ m' : Memory 4,m'.input=rest ∧ m'.stack 0=x.bits ∧
      m'.stack 1=[] ∧ m'.stack 2=[] ∧ m'.stack 3=[] ∧ m'.outputRev=[] ∧
      ∀ coins : Fin ((7*x.size+4)*2)→Bool,
        (compile program).run (encodeNat x++rest) coins=encode program ⟨none,m'⟩ := by
  let m : Memory 4 := ⟨encodeNat x++rest,0,fun _ => [],fun _ => 0,[]⟩
  have hi : m.input=List.replicate x.bits.length true++false::(x.bits++rest) := by
    simp [m,encodeNat,List.append_assoc]
  obtain ⟨m',hr,hi',h0,h1,h2,h3,ho⟩ := parse_word x.bits m rest hi rfl rfl
  refine ⟨m',hi',by simpa [m] using h0,h1,h2,h3,ho,?_⟩
  intro coins
  rw [run_eq]
  unfold run
  have he := fold_independent (List.ofFn fun i : Fin (7*x.size+4) => coins (second i)) (List.replicate (7*x.size+4) false) (by simp) (initial program (encodeNat x++rest))
  rw [he]
  change encode program (exec (7*x.size+4) (config .prefix m))=_
  simpa only [Nat.size_eq_bits_len] using congrArg (encode program) hr

end
end Contingency.BitModel.StackCode.ParseNat

 

 

 

namespace Contingency.BitModel.StackCode.PrepareMaximum
noncomputable section

def reg (i : Fin 4) : Fin 6 := i.castAdd 2

theorem reg_injective : Function.Injective reg := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 6 => x.val) h

abbrev parser : Program :=
  ⟨ParseNat.program.labels,6,ParseNat.program.start,fun q => Registers.op reg (ParseNat.program.code q)⟩

def program : Program := Sequence.program parser 4 0 (Transfer.code (0 : Fin 6) 4)

theorem parser_noCoin : ∀ q,NoCoin (parser.code q) := by
  intro q
  apply noCoin_registers
  change NoCoin (ParseNat.code ((Fintype.equivFin ParseNat.Q).symm q))
  cases (Fintype.equivFin ParseNat.Q).symm q <;> trivial

theorem noCoin : ∀ q,NoCoin (program.code q) := by
  apply noCoin_sequence _ _ _ _ parser_noCoin
  intro q
  fin_cases q <;> trivial

 

theorem prepare (N : ℕ) (rest : List Bool) :
    ∃ (t : ℕ) (m' : Memory 6),t≤9*N.size+6 ∧
      (∀ i : Fin 4,m'.stack (reg i)=[]) ∧
      m'.stack 4=IntegerDraw.rawMaximum N ∧ m'.stack 5=[] ∧
      m'.input=rest ∧ m'.outputRev=[] ∧
      ∀ coins : List Bool,coins.length=t →
        coins.foldl (fun c b => step program b c) (initial program (encodeNat N++rest))=⟨none,m'⟩ := by
  let xs := encodeNat N++rest
  let m₄ : Memory 4 := (initial ParseNat.program xs).memory
  have hi : m₄.input=List.replicate N.bits.length true++false::(N.bits++rest) := by
    simp [m₄,initial,xs,encodeNat,List.append_assoc]
  obtain ⟨m₄',hp,hi',h0,h1,h2,h3,ho⟩ := ParseNat.parse_word N.bits m₄ rest hi rfl rfl
  let T := 7*N.size+4
  have hp' : (List.replicate T false).foldl (fun c b => step ParseNat.program b c)
      (initial ParseNat.program xs)=⟨none,m₄'⟩ := by
    simpa only [ParseNat.exec,T,Nat.size_eq_bits_len,ParseNat.config,m₄,initial,ParseNat.program] using hp
  let c₆ := (List.replicate T false).foldl (fun c b => step parser b c) (initial parser xs)
  have hr₀ : Registers.ConfigRel ParseNat.program reg (initial ParseNat.program xs) (initial parser xs) :=
    ⟨rfl,fun _ => rfl,rfl,rfl,rfl⟩
  have hr := Registers.fold_rel ParseNat.program reg reg_injective (List.replicate T false) hr₀
  rw [hp'] at hr
  have hc : c₆.state=none := hr.1
  have hs : ∀ i : Fin 4,c₆.memory.stack (reg i)=m₄'.stack i := hr.2.1
  have hs0 : c₆.memory.stack 0=N.bits := by simpa [reg,m₄,initial] using (hs 0).trans h0
  have hs1 : c₆.memory.stack 1=[] := (hs 1).trans h1
  have hs2 : c₆.memory.stack 2=[] := (hs 2).trans h2
  have hs3 : c₆.memory.stack 3=[] := by simpa [reg,m₄,initial] using (hs 3).trans h3
  have frame (j : Fin 6) (hj : ∀ i,reg i≠j) : c₆.memory.stack j=[] :=
    Registers.fold_frame ParseNat.program reg (List.replicate T false) (initial parser xs) j hj
  have hs4 : c₆.memory.stack 4=[] := frame 4 (by intro i h; have hv := congrArg Fin.val h; have hi := i.isLt; change i.val=4 at hv; omega)
  have hs5 : c₆.memory.stack 5=[] := frame 5 (by intro i h; have hv := congrArg Fin.val h; have hi := i.isLt; change i.val=5 at hv; omega)
  obtain ⟨t,ht,hfirst⟩ := Sequence.deterministic_first_time parser
    (noCoin_deterministic parser parser_noCoin) (initial parser xs) T hc
  have hf := hfirst (List.replicate t false) (by simp)
  let m' := Transfer.memory (0 : Fin 6) 4 N.bits c₆.memory
  have hm := Transfer.memory_fields (0 : Fin 6) 4 (by decide) N.bits c₆.memory hs0
  refine ⟨t+(2*N.bits.length+2),m',?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [Nat.size_eq_bits_len]
    dsimp only [T] at ht
    omega
  · intro i
    fin_cases i
    · exact hm.1
    · exact (hm.2.2.1 1 (by decide) (by decide)).trans hs1
    · exact (hm.2.2.1 2 (by decide) (by decide)).trans hs2
    · exact (hm.2.2.1 3 (by decide) (by decide)).trans hs3
  · simpa only [m',IntegerDraw.rawMaximum,hs4,List.append_nil] using hm.2.1
  · exact (hm.2.2.1 5 (by decide) (by decide)).trans hs5
  · exact hm.2.2.2.1.trans (hr.2.2.1.trans hi')
  · exact hm.2.2.2.2.1.trans (hr.2.2.2.1.trans ho)
  · intro coins hlen
    rw [Sequence.deterministic_fold program (noCoin_deterministic program noCoin) _ _
      (List.replicate (t+(2*N.bits.length+2)) false) (by simpa using hlen)]
    rw [List.replicate_add]
    have hl := Sequence.link_run parser 4 0 (Transfer.code (0 : Fin 6) 4)
      (initial parser xs) (List.replicate t false) (List.replicate (2*N.bits.length+2) false) hf.1
    rw [hf.2] at hl
    change (List.replicate t false++List.replicate (2*N.bits.length+2) false).foldl
      (fun c b => step program b c) (initial program xs)=⟨none,m'⟩
    have ht_run := Transfer.run (0 : Fin 6) 4 (by decide) N.bits c₆.memory hs0
    change (List.replicate (2*N.bits.length+2) false).foldl
      (fun c b => step (Transfer.program (0 : Fin 6) 4) b c)
      (Transfer.config (0 : Fin 6) 4 0 c₆.memory)=⟨none,m'⟩ at ht_run
    change (List.replicate t false++List.replicate (2*N.bits.length+2) false).foldl
      (fun c b => step program b c) (initial program xs)=
        Sequence.right parser 4 0 (Transfer.code (0 : Fin 6) 4)
          ((List.replicate (2*N.bits.length+2) false).foldl
            (fun c b => step (Transfer.program (0 : Fin 6) 4) b c)
            (Transfer.config (0 : Fin 6) 4 0 c₆.memory)) at hl
    exact hl.trans (congrArg (fun c : Config (Transfer.program (0 : Fin 6) 4) =>
      Sequence.right parser 4 0 (Transfer.code (0 : Fin 6) 4) c) ht_run)

end
end Contingency.BitModel.StackCode.PrepareMaximum

 

 

 

namespace Contingency.BitModel.StackCode.PreparedIntegerCall
noncomputable section

abbrev callee : Program :=
  ⟨IntegerDraw.program.labels,6,IntegerDraw.program.start,
    fun q => Internal.op (IntegerDraw.program.code q)⟩

def program : Program := Sequence.program PrepareMaximum.program
  callee.labels callee.start callee.code

def result (c : Config callee) : Config program :=
  Sequence.right PrepareMaximum.program callee.labels callee.start callee.code c

 
theorem prepared_first (N : ℕ) (rest : List Bool) :
    ∃ (t : ℕ) (m : Memory 6),t≤9*N.size+6 ∧
      (∀ i : Fin 4,m.stack (PrepareMaximum.reg i)=[]) ∧
      m.stack 4=IntegerDraw.rawMaximum N ∧ m.stack 5=[] ∧
      m.input=rest ∧ m.outputRev=[] ∧
      ∀ a : List Bool,a.length=t →
        Sequence.FirstHalt PrepareMaximum.program
          (initial PrepareMaximum.program (encodeNat N++rest)) a ∧
        a.foldl (fun c b => step PrepareMaximum.program b c)
          (initial PrepareMaximum.program (encodeNat N++rest))=⟨none,m⟩ := by
  obtain ⟨T,m,hT,hw,hi,ho,he,hout,hr⟩ := PrepareMaximum.prepare N rest
  have hrun := hr (List.replicate T false) (by simp)
  obtain ⟨t,ht,hf⟩ := Sequence.deterministic_first_time PrepareMaximum.program
    (noCoin_deterministic _ PrepareMaximum.noCoin)
    (initial PrepareMaximum.program (encodeNat N++rest)) T
    (by rw [hrun])
  refine ⟨t,m,ht.trans hT,hw,hi,ho,he,hout,?_⟩
  intro a ha
  exact ⟨(hf a ha).1,((hf a ha).2).trans hrun⟩

 

theorem refinement (N : ℕ) (rest : List Bool) :
    ∃ t≤9*N.size+6,∀ a : List Bool,a.length=t → ∀ b : List Bool,
      ∃ c : Config callee,
        (a++b).foldl (fun c x => step program x c)
          (initial program (encodeNat N++rest))=result c ∧
        Internal.ConfigRel IntegerDraw.program
          (b.foldl (fun c x => step IntegerDraw.program x c)
            (initial IntegerDraw.program (IntegerDraw.rawMaximum N))) c ∧
        c.memory.input=rest ∧ c.memory.outputRev=[] := by
  obtain ⟨t,m,ht,hw,hi,ho,he,hout,hr⟩ := prepared_first N rest
  refine ⟨t,ht,?_⟩
  intro a ha b
  let start : Config callee := ⟨some callee.start,m⟩
  have hrel : Internal.ConfigRel IntegerDraw.program
      (initial IntegerDraw.program (IntegerDraw.rawMaximum N)) start := by
    refine ⟨rfl,?_,hi,ho⟩
    intro i
    exact hw i
  let c := b.foldl (fun c x => step callee x c) start
  have hc := Internal.fold_rel IntegerDraw.program b hrel
  have hf := Internal.fold_frame IntegerDraw.program b start
  refine ⟨c,?_,hc,hf.1.trans he,hf.2.1.trans hout⟩
  have hh := Sequence.link_run PrepareMaximum.program callee.labels callee.start callee.code
    (initial PrepareMaximum.program (encodeNat N++rest)) a b (hr a ha).1
  rw [(hr a ha).2] at hh
  exact hh

 

theorem tape_refinement (N : ℕ) (rest : List Bool) :
    ∃ t≤9*N.size+6,∀ (s : ℕ) (coins : Fin ((t+s)*2)→Bool),
      ∃ c : Config callee,
        (compile program).run (encodeNat N++rest) coins=encode program (result c) ∧
        Internal.ConfigRel IntegerDraw.program
          (((List.ofFn fun i : Fin (t+s) => coins (second i)).drop t).foldl
            (fun c x => step IntegerDraw.program x c)
            (initial IntegerDraw.program (IntegerDraw.rawMaximum N))) c ∧
        c.memory.input=rest ∧ c.memory.outputRev=[] := by
  obtain ⟨t,ht,hr⟩ := refinement N rest
  refine ⟨t,ht,?_⟩
  intro s coins
  let xs := List.ofFn fun i : Fin (t+s) => coins (second i)
  obtain ⟨c,hc,hm,hi,ho⟩ := hr (xs.take t) (by simp [xs]) (xs.drop t)
  rw [List.take_append_drop] at hc
  refine ⟨c,?_,hm,hi,ho⟩
  rw [run_eq]
  exact congrArg (encode program) hc

end
end Contingency.BitModel.StackCode.PreparedIntegerCall

 

 

 

namespace Contingency.BitModel.StackCode.InputCall
open Internal (work input)

def op {l w : ℕ} : Op l w→Op l (w+2)
  | .push i b q => .push (work i) b q
  | .pop i e z o => .pop (work i) e z o
  | .read e z o => .pop (input w) e z o
  | .coin z o => .coin z o
  | .emit b q => .emit b q
  | .jump q => .jump q
  | .halt => .halt

def program (P : Program) : Program := ⟨P.labels,P.work+2,P.start,fun q => op (P.code q)⟩

 

def MemoryRel {w : ℕ} (a : Memory w) (b : Memory (w+2)) : Prop :=
  (∀ i,b.stack (work i)=a.stack i) ∧
    b.stack (input w)=a.input ∧ b.outputRev=a.outputRev

theorem push_work {w : ℕ} {a : Memory w} {b : Memory (w+2)} (h : MemoryRel a b)
    (i : Fin w) (v : Bool) : MemoryRel (a.push i v) (b.push (work i) v) := by
  rcases h with ⟨hw,hi,ho⟩
  refine ⟨?_,?_,?_⟩
  · intro j
    simp [Memory.push,Function.update_apply,hw]
  · simpa [Memory.push] using hi
  · simpa [Memory.push] using ho

theorem pop_work {w : ℕ} {a : Memory w} {b : Memory (w+2)} (h : MemoryRel a b)
    (i : Fin w) : MemoryRel (a.pop i) (b.pop (work i)) := by
  rcases h with ⟨hw,hi,ho⟩
  refine ⟨?_,?_,?_⟩
  · intro j
    simp [Memory.pop,Function.update_apply,hw]
  · simpa [Memory.pop] using hi
  · simpa [Memory.pop] using ho

theorem read_input {w : ℕ} {a : Memory w} {b : Memory (w+2)} (h : MemoryRel a b) :
    MemoryRel a.read (b.pop (input w)) := by
  rcases h with ⟨hw,hi,ho⟩
  refine ⟨?_,?_,?_⟩
  · intro j
    simpa [Memory.pop,Memory.read] using hw j
  · simp [Memory.pop,Memory.read,hi]
  · simpa [Memory.pop,Memory.read] using ho

theorem emit_output {w : ℕ} {a : Memory w} {b : Memory (w+2)} (h : MemoryRel a b) (v : Bool) :
    MemoryRel {a with outputRev:=v::a.outputRev} {b with outputRev:=v::b.outputRev} := by
  exact ⟨h.1,h.2.1,congrArg (v::·) h.2.2⟩

theorem effect_rel {l w : ℕ} (code : Op l w) (coin : Bool)
    {a : Memory w} {b : Memory (w+2)} (h : MemoryRel a b) :
    (effect (op code) coin b).1=(effect code coin a).1 ∧
      MemoryRel (effect code coin a).2 (effect (op code) coin b).2 := by
  cases code with
  | push i v q => exact ⟨rfl,push_work h i v⟩
  | pop i e z o => exact ⟨by simp [op,effect,h.1 i],pop_work h i⟩
  | read e z o => exact ⟨by simp [op,effect,h.2.1],read_input h⟩
  | coin z o => exact ⟨rfl,h⟩
  | emit v q => exact ⟨rfl,emit_output h v⟩
  | jump q => exact ⟨rfl,h⟩
  | halt => exact ⟨rfl,h⟩

def ConfigRel (P : Program) (a : Config P) (b : Config (program P)) : Prop :=
  b.state=a.state ∧ MemoryRel a.memory b.memory

theorem step_rel (P : Program) (coin : Bool) {a : Config P} {b : Config (program P)}
    (h : ConfigRel P a b) : ConfigRel P (step P coin a) (step (program P) coin b) := by
  rcases a with ⟨sa,ma⟩
  rcases b with ⟨sb,mb⟩
  obtain ⟨hs,hm⟩ := h
  dsimp only at hs hm
  subst sb
  cases sa with
  | none => exact ⟨rfl,hm⟩
  | some pc => exact effect_rel (P.code pc) coin hm

theorem fold_rel (P : Program) (coins : List Bool) {a : Config P} {b : Config (program P)}
    (h : ConfigRel P a b) :
    ConfigRel P (coins.foldl (fun c v => step P v c) a)
      (coins.foldl (fun c v => step (program P) v c) b) := by
  induction coins generalizing a b with
  | nil => exact h
  | cons v coins ih => exact ih (step_rel P v h)

end Contingency.BitModel.StackCode.InputCall

 

 

 

open scoped BigOperators
open Filter
namespace Contingency.BitModel.StackCode.EncodedInteger
noncomputable section

abbrev callee : Program :=
  ⟨IntegerDraw.program.labels,6,IntegerDraw.program.start,
    fun q => InputCall.op (IntegerDraw.program.code q)⟩

def program : Program := Sequence.program PrepareMaximum.program
  callee.labels callee.start callee.code

def result (c : Config callee) : Config program :=
  Sequence.right PrepareMaximum.program callee.labels callee.start callee.code c

 

theorem refinement (N : ℕ) (rest : List Bool) :
    ∃ t≤9*N.size+6,∀ (s : ℕ) (f : Fin (t+s)→Bool),
      ((run program (encodeNat N++rest) f).state=none ↔
        (run IntegerDraw.program (IntegerDraw.rawMaximum N) (fun i => f (Fin.natAdd t i))).state=none) ∧
      (run program (encodeNat N++rest) f).memory.outputRev=
        (run IntegerDraw.program (IntegerDraw.rawMaximum N) (fun i => f (Fin.natAdd t i))).memory.outputRev := by
  obtain ⟨t,m,ht,hw,hi,ho,he,hout,hr⟩ := PreparedIntegerCall.prepared_first N rest
  refine ⟨t,ht,?_⟩
  intro s f
  let a := List.ofFn fun i : Fin t => f (i.castAdd s)
  let b := List.ofFn fun i : Fin s => f (Fin.natAdd t i)
  have ha := hr a (by simp [a])
  let start : Config callee := ⟨some callee.start,m⟩
  have hrel : InputCall.ConfigRel IntegerDraw.program
      (initial IntegerDraw.program (IntegerDraw.rawMaximum N)) start := by
    refine ⟨rfl,?_,hi,hout⟩
    intro i
    exact hw i
  have hc := InputCall.fold_rel IntegerDraw.program b hrel
  have hh := Sequence.link_run PrepareMaximum.program callee.labels callee.start callee.code
    (initial PrepareMaximum.program (encodeNat N++rest)) a b ha.1
  rw [ha.2] at hh
  have hr' : run program (encodeNat N++rest) f=
      result (b.foldl (fun c x => step callee x c) start) := by
    unfold run
    rw [List.ofFn_add]
    exact hh
  rw [hr']
  constructor
  · change Option.map (Fin.natAdd PrepareMaximum.program.labels)
        (b.foldl (fun c x => step callee x c) start).state=none ↔ _
    rw [Option.map_eq_none_iff]
    exact (congrArg (fun v => v=none) hc.1).to_iff
  · exact hc.2.2.2

 
theorem shifted_laws (N : ℕ) (rest : List Bool) :
    ∃ t≤9*N.size+6,∀ s : ℕ,
      (∀ out,mass program (encodeNat N++rest) out (t+s)=
        mass IntegerDraw.program (IntegerDraw.rawMaximum N) out s) ∧
      tail program (encodeNat N++rest) (t+s)=
        tail IntegerDraw.program (IntegerDraw.rawMaximum N) s := by
  classical
  obtain ⟨t,ht,hr⟩ := refinement N rest
  refine ⟨t,ht,?_⟩
  intro s
  have hi : Function.Injective (Fin.natAdd t : Fin s→Fin (t+s)) := by
    intro i j h
    simpa using h
  constructor
  · intro out
    unfold mass
    simp only [(hr s _).1,(hr s _).2]
    simpa only [Fintype.card_fin,Function.comp_def] using CoordinateLaw.probability_restrict (Fin.natAdd t) hi
      (fun f => (run IntegerDraw.program (IntegerDraw.rawMaximum N) f).state=none ∧
        (run IntegerDraw.program (IntegerDraw.rawMaximum N) f).memory.outputRev.reverse=out)
  · unfold tail
    simp only [ne_eq,(hr s _).1]
    simpa only [Fintype.card_fin,Function.comp_def] using CoordinateLaw.probability_restrict (Fin.natAdd t) hi
      (fun f => (run IntegerDraw.program (IntegerDraw.rawMaximum N) f).state≠none)

 

theorem stack_safe (N : ℕ) (rest : List Bool) {s : ℕ} (f : Fin s→Bool)
    (h : (run program (encodeNat N++rest) f).state=none) :
    ∃ u : Fin (N+1),(run program (encodeNat N++rest) f).memory.outputRev.reverse=
      IntegerDraw.integerWord N u := by
  obtain ⟨t,ht,hr⟩ := refinement N rest
  let g : Fin (t+s)→Bool := fun i => if h : i.val<s then f ⟨i,h⟩ else false
  have hg : (fun i : Fin s => g ⟨i,lt_of_lt_of_le i.isLt (by omega : s≤t+s)⟩)=f := by
    funext i
    simp [g,i.isLt]
  have hp := run_prefix_halt program (encodeNat N++rest) s (t+s) (by omega) g (by simpa [hg] using h)
  rw [hg] at hp
  have hh := (hr s g).1.mp (by rw [hp]; exact h)
  obtain ⟨u,hu⟩ := IntegerDraw.stack_safe (IntegerDraw.rawMaximum N)
    (fun i => g (Fin.natAdd t i)) hh
  refine ⟨⟨u,by simpa using u.isLt⟩,?_⟩
  rw [← hp,(hr s g).2]
  exact hu

end
end Contingency.BitModel.StackCode.EncodedInteger

 

 

 

open scoped BigOperators
open Filter
namespace Contingency.BitModel.StackCode.EncodedInteger
noncomputable section

def machine : Machine := compile program

theorem stack_summable (N : ℕ) (rest : List Bool) :
    Summable (tail program (encodeNat N++rest)) := by
  obtain ⟨t,ht,hl⟩ := shifted_laws N rest
  apply (summable_nat_add_iff t).1
  simpa only [Nat.add_comm, (hl _).2] using
    IntegerDraw.stack_summable (IntegerDraw.rawMaximum N)

theorem stack_expected (N : ℕ) (rest : List Bool) :
    (∑' s,tail program (encodeNat N++rest) s)≤35*(N.size:ℝ)+21 := by
  obtain ⟨t,ht,hl⟩ := shifted_laws N rest
  have hs := stack_summable N rest
  rw [← hs.sum_add_tsum_nat_add t]
  have hb : (∑ s∈Finset.range t,tail program (encodeNat N++rest) s)≤(t:ℝ) := by
    calc
      _ ≤ ∑ s∈Finset.range t,(1:ℝ) := by
        exact Finset.sum_le_sum fun _ _ => IntegerDraw.tail_le_one _ _ _
      _ = _ := by simp
  have he : (∑' s,tail program (encodeNat N++rest) (s+t))=
      ∑' s,tail IntegerDraw.program (IntegerDraw.rawMaximum N) s := by
    congr 1
    funext s
    simpa only [Nat.add_comm] using (hl s).2
  rw [he]
  have hw : 2^(IntegerDraw.rawMaximum N).length≤
      2*(BinaryTrial.beValue (IntegerDraw.rawMaximum N)+1) := by
    simpa using IntegerDraw.minimal_width N
  have hi := IntegerDraw.stack_linear_expected (IntegerDraw.rawMaximum N) hw
  simp only [IntegerDraw.rawMaximum_length] at hi
  have ht' : (t:ℝ)≤9*(N.size:ℝ)+6 := by exact_mod_cast ht
  push_cast at hi
  linarith

theorem stack_uniform (N : ℕ) (rest : List Bool) (u : Fin (N+1)) :
    Tendsto (mass program (encodeNat N++rest) (IntegerDraw.integerWord N u))
      atTop (nhds (1/(N+1:ℝ))) := by
  obtain ⟨t,ht,hl⟩ := shifted_laws N rest
  apply (tendsto_add_atTop_iff_nat t).1
  have he : (fun s => mass program (encodeNat N++rest) (IntegerDraw.integerWord N u) (s+t))=
      mass IntegerDraw.program (IntegerDraw.rawMaximum N) (IntegerDraw.integerWord N u) := by
    funext s
    simpa only [Nat.add_comm] using (hl s).1 (IntegerDraw.integerWord N u)
  rw [he]
  simpa only [IntegerDraw.rawMaximum_value,IntegerDraw.integerWord] using
    IntegerDraw.stack_uniform (IntegerDraw.rawMaximum N) ⟨u,by simpa using u.isLt⟩

 

theorem integer_sampler (N : ℕ) (rest : List Bool) :
    (∀ (t : ℕ) (coins : Fin t→Bool),(machine.run (encodeNat N++rest) coins).state=none →
      ∃ u : Fin (N+1),(machine.run (encodeNat N++rest) coins).outputRev.reverse=IntegerDraw.integerWord N u) ∧
    Tendsto (machine.tail (encodeNat N++rest)) atTop (nhds 0) ∧
    (∀ u : Fin (N+1),Tendsto (machine.mass (encodeNat N++rest) (IntegerDraw.integerWord N u))
      atTop (nhds (1/(N+1:ℝ)))) ∧
    Summable (machine.tail (encodeNat N++rest)) ∧
    (∑' t,machine.tail (encodeNat N++rest) t)≤70*(N.size:ℝ)+42 := by
  have hs := tail_summable_compile program (encodeNat N++rest) (stack_summable N rest)
  refine ⟨?_,hs.tendsto_atTop_zero,?_,hs,?_⟩
  · exact safe_compile program (encodeNat N++rest)
      (fun out => ∃ u : Fin (N+1),out=IntegerDraw.integerWord N u)
      (fun _ f h => stack_safe N rest f h)
  · intro u
    exact mass_limit_compile program (encodeNat N++rest) (IntegerDraw.integerWord N u) _
      (stack_uniform N rest u)
  · rw [machine,expected_compile program (encodeNat N++rest) (stack_summable N rest)]
    linarith [stack_expected N rest]

end
end Contingency.BitModel.StackCode.EncodedInteger

end

end OAI
