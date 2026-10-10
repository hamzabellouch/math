import Mathlib
import OAI.Probability.Contingency.BinaryAddition

namespace OAI

/-! Stack Sequence. -/

noncomputable section


namespace Contingency.BitModel.StackCode.Sequence

variable {l L w : ℕ}

def relabel (f : Fin l→Fin L) (stop : Op L w) : Op l w→Op L w
  | .push i b q => .push i b (f q)
  | .pop i e z o => .pop i (f e) (f z) (f o)
  | .read e z o => .read (f e) (f z) (f o)
  | .coin z o => .coin (f z) (f o)
  | .emit b q => .emit b (f q)
  | .jump q => .jump (f q)
  | .halt => stop

def next (f : Fin l→Fin L) (stop : Option (Fin L)) : Option (Fin l)→Option (Fin L)
  | none => stop
  | some q => some (f q)

theorem branch_map (f : Fin l→Fin L) (e z o : Fin l) (b : Option Bool) :
    branch (f e) (f z) (f o) b=f (branch e z o b) := by
  cases b with
  | none => rfl
  | some b => cases b <;> rfl

theorem effect_jump (f : Fin l→Fin L) (q : Fin L) (op : Op l w) (b : Bool) (m : Memory w) :
    effect (relabel f (.jump q) op) b m=(next f (some q) (effect op b m).1,(effect op b m).2) := by
  cases op <;> simp only [relabel,effect,next,branch_map]
  case coin z o => cases b <;> rfl

theorem effect_halt (f : Fin l→Fin L) (op : Op l w) (b : Bool) (m : Memory w) :
    effect (relabel f .halt op) b m=(Option.map f (effect op b m).1,(effect op b m).2) := by
  cases op <;> simp only [relabel,effect,Option.map_some,Option.map_none,branch_map]
  case coin z o => cases b <;> rfl

variable (P : Program) (q : ℕ) (start : Fin q) (code : Fin q→Op q P.work)

def rightProgram : Program := ⟨q,P.work,start,code⟩

def program : Program :=
  ⟨P.labels+q,P.work,P.start.castAdd q,
    Fin.addCases
      (fun i => relabel (Fin.castAdd q) (.jump (Fin.natAdd P.labels start)) (P.code i))
      (fun i => relabel (Fin.natAdd P.labels) .halt (code i))⟩

def left (cfg : Config P) : Config (program P q start code) :=
  ⟨next (Fin.castAdd q) (some (Fin.natAdd P.labels start)) cfg.state,cfg.memory⟩

def right (cfg : Config (rightProgram P q start code)) : Config (program P q start code) :=
  ⟨Option.map (Fin.natAdd P.labels) cfg.state,cfg.memory⟩

theorem step_left (cfg : Config P) (b : Bool) (live : cfg.state≠none) :
    step (program P q start code) b (left P q start code cfg)=
      left P q start code (step P b cfg) := by
  rcases cfg with ⟨s,m⟩
  cases s with
  | none => exact (live rfl).elim
  | some pc =>
    simp only [left,next,step,program,Fin.addCases_left,effect_jump]

 theorem step_right (cfg : Config (rightProgram P q start code)) (b : Bool) :
    step (program P q start code) b (right P q start code cfg)=
      right P q start code (step (rightProgram P q start code) b cfg) := by
  rcases cfg with ⟨s,m⟩
  cases s with
  | none => rfl
  | some pc =>
    change Fin q at pc
    change Memory P.work at m
    change (let e := effect ((program P q start code).code (Fin.natAdd P.labels pc)) b m; (⟨e.1,e.2⟩ : Config (program P q start code))) =
      ⟨Option.map (Fin.natAdd P.labels) (effect (code pc) b m).1,(effect (code pc) b m).2⟩
    simp only [program,Fin.addCases_right,effect_halt]

 
def FirstHalt (cfg : Config P) : List Bool→Prop
  | [] => cfg.state=none
  | b::bs => cfg.state≠none ∧ FirstHalt (step P b cfg) bs

theorem firstHalt_result (cfg : Config P) (bs : List Bool) (h : FirstHalt P cfg bs) :
    (bs.foldl (fun c b => step P b c) cfg).state=none := by
  induction bs generalizing cfg with
  | nil => exact h
  | cons b bs ih => exact ih _ h.2

theorem fold_left (cfg : Config P) (bs : List Bool) (h : FirstHalt P cfg bs) :
    bs.foldl (fun c b => step (program P q start code) b c) (left P q start code cfg)=
      left P q start code (bs.foldl (fun c b => step P b c) cfg) := by
  induction bs generalizing cfg with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons]
    rw [step_left P q start code cfg b h.1]
    exact ih _ h.2

theorem fold_right (cfg : Config (rightProgram P q start code)) (bs : List Bool) :
    bs.foldl (fun c b => step (program P q start code) b c) (right P q start code cfg)=
      right P q start code (bs.foldl (fun c b => step (rightProgram P q start code) b c) cfg) := by
  induction bs generalizing cfg with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons]
    rw [step_right P q start code]
    exact ih _

 

theorem link_run (cfg : Config P) (a b : List Bool) (h : FirstHalt P cfg a) :
    (a++b).foldl (fun c v => step (program P q start code) v c) (left P q start code cfg)=
      right P q start code (b.foldl (fun c v => step (rightProgram P q start code) v c)
        ⟨some start,(a.foldl (fun c v => step P v c) cfg).memory⟩) := by
  rw [List.foldl_append,fold_left P q start code cfg a h]
  have hs := firstHalt_result P cfg a h
  have he : left P q start code (a.foldl (fun c v => step P v c) cfg)=
      right P q start code ⟨some start,(a.foldl (fun c v => step P v c) cfg).memory⟩ := by
    simp only [left,right,next,hs]
    rfl
  rw [he,fold_right]

end Contingency.BitModel.StackCode.Sequence

 

 

namespace Contingency.BitModel.StackCode.Sequence

variable (P : Program)

theorem halted_fold (cfg : Config P) (h : cfg.state=none) (xs : List Bool) :
    xs.foldl (fun c b => step P b c) cfg=cfg := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hs : step P x cfg=cfg := by rcases cfg with ⟨s,m⟩; dsimp only at h; subst s; rfl
    simpa only [List.foldl_cons,hs] using ih

 

theorem first_prefix (cfg : Config P) (xs : List Bool)
    (h : (xs.foldl (fun c b => step P b c) cfg).state=none) :
    ∃ a b : List Bool,xs=a++b ∧ FirstHalt P cfg a ∧
      a.foldl (fun c b => step P b c) cfg=xs.foldl (fun c b => step P b c) cfg := by
  induction xs generalizing cfg with
  | nil => exact ⟨[],[],rfl,h,rfl⟩
  | cons x xs ih =>
    by_cases hc : cfg.state=none
    · refine ⟨[],x::xs,rfl,hc,?_⟩
      exact (halted_fold P cfg hc (x::xs)).symm
    · obtain ⟨a,b,hab,hh,he⟩ := ih (step P x cfg) h
      exact ⟨x::a,b,by simp [hab],⟨hc,hh⟩,he⟩

def Deterministic : Prop := ∀ (cfg : Config P) (a b : Bool),step P a cfg=step P b cfg

theorem deterministic_fold (hd : Deterministic P) (cfg : Config P) (a b : List Bool)
    (hl : a.length=b.length) :
    a.foldl (fun c v => step P v c) cfg=b.foldl (fun c v => step P v c) cfg := by
  induction a generalizing cfg b with
  | nil => have hb : b=[] := List.length_eq_zero_iff.mp hl.symm; subst b; rfl
  | cons a as ih =>
    cases b with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hl
      simp only [List.foldl_cons]
      rw [hd cfg a b]
      exact ih _ _ hl

theorem deterministic_first (hd : Deterministic P) (cfg : Config P) (a b : List Bool)
    (hl : a.length=b.length) (h : FirstHalt P cfg a) : FirstHalt P cfg b := by
  induction a generalizing cfg b with
  | nil => have hb : b=[] := List.length_eq_zero_iff.mp hl.symm; subst b; exact h
  | cons a as ih =>
    cases b with
    | nil => simp at hl
    | cons b bs =>
      refine ⟨h.1,?_⟩
      rw [← hd cfg a b]
      exact ih _ _ (by simpa using hl) h.2

 

theorem deterministic_first_time (hd : Deterministic P) (cfg : Config P) (T : ℕ)
    (h : ((List.replicate T false).foldl (fun c b => step P b c) cfg).state=none) :
    ∃ t≤T,∀ coins : List Bool,coins.length=t → FirstHalt P cfg coins ∧
      coins.foldl (fun c b => step P b c) cfg=
        (List.replicate T false).foldl (fun c b => step P b c) cfg := by
  obtain ⟨a,b,he,ha,hr⟩ := first_prefix P cfg (List.replicate T false) h
  refine ⟨a.length,?_,?_⟩
  · have hh := congrArg List.length he
    simp only [List.length_replicate,List.length_append] at hh
    omega
  · intro coins hc
    exact ⟨deterministic_first P hd cfg a coins hc.symm ha,
      (deterministic_fold P hd cfg coins a hc).trans hr⟩

variable (q : ℕ) (start : Fin q) (code : Fin q→Op q P.work)

 

theorem tape_link (cfg : Config P) {t : ℕ} (coins : Fin (t*2)→Bool) (k : ℕ)
    (h : FirstHalt P cfg ((List.ofFn fun i : Fin t => coins (second i)).take k)) :
    (List.ofFn coins).foldl (fun c b => (compile (program P q start code)).step b c)
      (encode (program P q start code) (left P q start code cfg))=
      encode (program P q start code)
        (right P q start code (((List.ofFn fun i : Fin t => coins (second i)).drop k).foldl
          (fun c b => step (rightProgram P q start code) b c)
          ⟨some start,(((List.ofFn fun i : Fin t => coins (second i)).take k).foldl
             (fun c b => step P b c) cfg).memory⟩)) := by
  rw [Internal.tape_fold]
  have hs := link_run P q start code cfg
    ((List.ofFn fun i : Fin t => coins (second i)).take k)
    ((List.ofFn fun i : Fin t => coins (second i)).drop k) h
  rw [List.take_append_drop] at hs
  rw [hs]

end Contingency.BitModel.StackCode.Sequence

 

 

 

namespace Contingency.BitModel.StackCode.Registers

variable {l w v : ℕ}

def op (f : Fin w→Fin v) : Op l w→Op l v
  | .push i b q => .push (f i) b q
  | .pop i e z o => .pop (f i) e z o
  | .read e z o => .read e z o
  | .coin z o => .coin z o
  | .emit b q => .emit b q
  | .jump q => .jump q
  | .halt => .halt

def program (P : Program) (f : Fin P.work→Fin v) : Program :=
  ⟨P.labels,v,P.start,fun q => op f (P.code q)⟩

def MemoryRel (f : Fin w→Fin v) (a : Memory w) (b : Memory v) : Prop :=
  (∀ i,b.stack (f i)=a.stack i) ∧ b.input=a.input ∧
    b.outputRev=a.outputRev ∧ b.consumed=a.consumed

theorem push_rel (f : Fin w→Fin v) (hf : Function.Injective f)
    {a : Memory w} {b : Memory v} (h : MemoryRel f a b) (i : Fin w) (x : Bool) :
    MemoryRel f (a.push i x) (b.push (f i) x) := by
  refine ⟨?_,h.2⟩
  intro j
  simp [Memory.push,Function.update_apply,hf.eq_iff,h.1]

theorem pop_rel (f : Fin w→Fin v) (hf : Function.Injective f)
    {a : Memory w} {b : Memory v} (h : MemoryRel f a b) (i : Fin w) :
    MemoryRel f (a.pop i) (b.pop (f i)) := by
  refine ⟨?_,h.2⟩
  intro j
  simp [Memory.pop,Function.update_apply,hf.eq_iff,h.1]

theorem read_rel (f : Fin w→Fin v)
    {a : Memory w} {b : Memory v} (h : MemoryRel f a b) :
    MemoryRel f a.read b.read := by
  exact ⟨h.1,congrArg List.tail h.2.1,h.2.2.1,congrArg (·+1) h.2.2.2⟩

theorem effect_rel (f : Fin w→Fin v) (hf : Function.Injective f) (code : Op l w) (coin : Bool)
    {a : Memory w} {b : Memory v} (h : MemoryRel f a b) :
    (effect (op f code) coin b).1=(effect code coin a).1 ∧
      MemoryRel f (effect code coin a).2 (effect (op f code) coin b).2 := by
  cases code with
  | push i x q => exact ⟨rfl,push_rel f hf h i x⟩
  | pop i e z o => exact ⟨by simp [op,effect,h.1],pop_rel f hf h i⟩
  | read e z o => exact ⟨by simp [op,effect,h.2.1],read_rel f h⟩
  | coin z o => exact ⟨rfl,h⟩
  | emit x q => exact ⟨rfl,h.1,h.2.1,congrArg (x::·) h.2.2.1,h.2.2.2⟩
  | jump q => exact ⟨rfl,h⟩
  | halt => exact ⟨rfl,h⟩

def ConfigRel (P : Program) (f : Fin P.work→Fin v)
    (a : Config P) (b : Config (program P f)) : Prop :=
  b.state=a.state ∧ MemoryRel f a.memory b.memory

theorem step_rel (P : Program) (f : Fin P.work→Fin v) (hf : Function.Injective f)
    (coin : Bool) {a : Config P} {b : Config (program P f)} (h : ConfigRel P f a b) :
    ConfigRel P f (step P coin a) (step (program P f) coin b) := by
  rcases a with ⟨s,a⟩
  rcases b with ⟨t,b⟩
  obtain ⟨hs,hr⟩ := h
  dsimp only at hs hr
  subst t
  cases s with
  | none => exact ⟨rfl,hr⟩
  | some q => exact effect_rel f hf (P.code q) coin hr

theorem fold_rel (P : Program) (f : Fin P.work→Fin v) (hf : Function.Injective f)
    (coins : List Bool) {a : Config P} {b : Config (program P f)} (h : ConfigRel P f a b) :
    ConfigRel P f (coins.foldl (fun c v => step P v c) a)
      (coins.foldl (fun c v => step (program P f) v c) b) := by
  induction coins generalizing a b with
  | nil => exact h
  | cons x xs ih => exact ih (step_rel P f hf x h)

theorem effect_frame (f : Fin w→Fin v) (code : Op l w) (coin : Bool) (m : Memory v)
    (j : Fin v) (hj : ∀ i,f i≠j) : (effect (op f code) coin m).2.stack j=m.stack j := by
  cases code <;> simp [op,effect,Memory.push,Memory.pop,Memory.read,fun i => (hj i).symm]

theorem step_frame (P : Program) (f : Fin P.work→Fin v) (coin : Bool)
    (cfg : Config (program P f)) (j : Fin v) (hj : ∀ i,f i≠j) :
    (step (program P f) coin cfg).memory.stack j=cfg.memory.stack j := by
  rcases cfg with ⟨s,m⟩
  cases s with
  | none => rfl
  | some q => exact effect_frame f (P.code q) coin m j hj

theorem fold_frame (P : Program) (f : Fin P.work→Fin v) (coins : List Bool)
    (cfg : Config (program P f)) (j : Fin v) (hj : ∀ i,f i≠j) :
    (coins.foldl (fun c x => step (program P f) x c) cfg).memory.stack j=cfg.memory.stack j := by
  induction coins generalizing cfg with
  | nil => rfl
  | cons x xs ih => exact (ih (step (program P f) x cfg)).trans (step_frame P f x cfg j hj)

 

theorem tape_refinement (P : Program) (f : Fin P.work→Fin v) (hf : Function.Injective f)
    {a : Config P} {b : Config (program P f)} (h : ConfigRel P f a b)
    {t : ℕ} (coins : Fin (t*2)→Bool) :
    ∃ b' : Config (program P f),
      (List.ofFn coins).foldl (fun c x => (compile (program P f)).step x c) (encode (program P f) b)=
        encode (program P f) b' ∧
      ConfigRel P f ((List.ofFn fun i : Fin t => coins (second i)).foldl (fun c x => step P x c) a) b' ∧
      ∀ j,(∀ i,f i≠j) → b'.memory.stack j=b.memory.stack j := by
  let xs := List.ofFn fun i : Fin t => coins (second i)
  refine ⟨xs.foldl (fun c x => step (program P f) x c) b,Internal.tape_fold _ _ coins,
    fold_rel P f hf xs h,?_⟩
  exact fun j hj => fold_frame P f xs b j hj

end Contingency.BitModel.StackCode.Registers

 

 

 

namespace Contingency.BitModel.StackCode.Transfer

variable {w : ℕ} (src dst : Fin w)

def code : Fin 4→Op 4 w
  | 0 => .pop src 3 1 2
  | 1 => .push dst false 0
  | 2 => .push dst true 0
  | _ => .halt

def program : Program := ⟨4,w,0,code src dst⟩
def config (q : Fin 4) (m : Memory w) : Config (program src dst) := ⟨some q,m⟩
def exec (n : ℕ) (cfg : Config (program src dst)) : Config (program src dst) :=
  (List.replicate n false).foldl (fun c b => step (program src dst) b c) cfg

theorem exec_add (s t : ℕ) (cfg : Config (program src dst)) :
    exec src dst (s+t) cfg=exec src dst t (exec src dst s cfg) := by
  simp only [exec,List.replicate_add,List.foldl_append]

def memory : List Bool→Memory w→Memory w
  | [],m => m.pop src
  | b::bs,m => memory bs ((m.pop src).push dst b)

theorem two_steps (m : Memory w) (b : Bool) (bs : List Bool) (h : m.stack src=b::bs) :
    exec src dst 2 (config src dst 0 m)=config src dst 0 ((m.pop src).push dst b) := by
  cases b <;> simp [exec,step,config,program,code,effect,branch,h,List.replicate_succ]

theorem empty_run (m : Memory w) (h : m.stack src=[]) :
    exec src dst 2 (config src dst 0 m)=⟨none,m.pop src⟩ := by
  simp [exec,step,config,program,code,effect,branch,h,List.replicate_succ]

theorem run (hij : src≠dst) (bs : List Bool) (m : Memory w) (h : m.stack src=bs) :
    exec src dst (2*bs.length+2) (config src dst 0 m)=⟨none,memory src dst bs m⟩ := by
  induction bs generalizing m with
  | nil => exact empty_run src dst m h
  | cons b bs ih =>
    have he : 2*(b::bs).length+2=2+(2*bs.length+2) := by simp; omega
    rw [he,exec_add,two_steps src dst m b bs h,ih]
    · rfl
    · simp [Memory.push,Memory.pop,h,hij]

theorem memory_fields (hij : src≠dst) (bs : List Bool) (m : Memory w) (h : m.stack src=bs) :
    (memory src dst bs m).stack src=[] ∧
    (memory src dst bs m).stack dst=bs.reverse++m.stack dst ∧
    (∀ i,i≠src → i≠dst → (memory src dst bs m).stack i=m.stack i) ∧
    (memory src dst bs m).input=m.input ∧
    (memory src dst bs m).outputRev=m.outputRev ∧
    (memory src dst bs m).consumed=m.consumed := by
  induction bs generalizing m with
  | nil =>
    refine ⟨by simp [memory,Memory.pop,h],by simp [memory,Memory.pop,hij.symm],?_,rfl,rfl,rfl⟩
    intro i hi hj
    simp [memory,Memory.pop,hi]
  | cons b bs ih =>
    have hs : ((m.pop src).push dst b).stack src=bs := by simp [Memory.pop,Memory.push,h,hij]
    have hh := ih ((m.pop src).push dst b) hs
    refine ⟨hh.1,?_,?_,hh.2.2.2⟩
    · simpa [memory,Memory.pop,Memory.push,hij.symm,List.reverse_cons,List.append_assoc] using hh.2.1
    · intro i hi hj
      simpa [memory,Memory.pop,Memory.push,hi,hj] using hh.2.2.1 i hi hj

theorem deterministic : Sequence.Deterministic (program src dst) := by
  intro cfg a b
  rcases cfg with ⟨s,m⟩
  cases s with
  | none => rfl
  | some q =>
    change Fin 4 at q
    fin_cases q <;> rfl

 

theorem tape (hij : src≠dst) (bs : List Bool) (m : Memory w) (h : m.stack src=bs)
    (coins : Fin ((2*bs.length+2)*2)→Bool) :
    (List.ofFn coins).foldl (fun c b => (compile (program src dst)).step b c)
      (encode (program src dst) (config src dst 0 m))=
        encode (program src dst) ⟨none,memory src dst bs m⟩ := by
  rw [Internal.tape_fold]
  rw [Sequence.deterministic_fold _ (deterministic src dst) _ _
      (List.replicate (2*bs.length+2) false) (by simp)]
  exact congrArg (encode (program src dst)) (run src dst hij bs m h)

end Contingency.BitModel.StackCode.Transfer

 

 

namespace Contingency.BitModel.StackCode

 
def NoCoin {l w : ℕ} : Op l w→Prop
  | .coin _ _ => False
  | _ => True

theorem noCoin_effect {l w : ℕ} (op : Op l w) (h : NoCoin op) (a b : Bool) (m : Memory w) :
    effect op a m=effect op b m := by
  cases op <;> try rfl
  exact h.elim

theorem noCoin_deterministic (P : Program) (h : ∀ q,NoCoin (P.code q)) : Sequence.Deterministic P := by
  intro cfg a b
  rcases cfg with ⟨s,m⟩
  cases s with
  | none => rfl
  | some q =>
    change (⟨(effect (P.code q) a m).1,(effect (P.code q) a m).2⟩ : Config P)=
      ⟨(effect (P.code q) b m).1,(effect (P.code q) b m).2⟩
    rw [noCoin_effect _ (h q) a b m]

theorem noCoin_registers {l w v : ℕ} (f : Fin w→Fin v) (op : Op l w) (h : NoCoin op) :
    NoCoin (Registers.op f op) := by
  cases op <;> exact h

theorem noCoin_relabel {l L w : ℕ} (f : Fin l→Fin L) (stop : Op L w) (hs : NoCoin stop)
    (op : Op l w) (h : NoCoin op) : NoCoin (Sequence.relabel f stop op) := by
  cases op <;> first | exact h | exact hs

theorem noCoin_sequence (P : Program) (q : ℕ) (start : Fin q) (code : Fin q→Op q P.work)
    (hp : ∀ i,NoCoin (P.code i)) (hq : ∀ i,NoCoin (code i)) :
    ∀ i,NoCoin ((Sequence.program P q start code).code i) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [Sequence.program,Fin.addCases_left] using
      noCoin_relabel (Fin.castAdd q) (.jump (Fin.natAdd P.labels start)) trivial (P.code j) (hp j)
  · intro j
    simpa only [Sequence.program,Fin.addCases_right] using
      noCoin_relabel (Fin.natAdd P.labels) .halt trivial (code j) (hq j)

end Contingency.BitModel.StackCode

 

 

 

namespace Contingency.BitModel.StackCode.ParseNat
noncomputable section

inductive Q | prefix | count | data | bit | store (b : Bool) | restore | place (b : Bool) | done
  deriving DecidableEq,Fintype

def label (q : Q) : Fin (Fintype.card Q) := Fintype.equivFin Q q

def code : Q→Op (Fintype.card Q) 4
  | .prefix => .read (label .done) (label .data) (label .count)
  | .count => .push 2 false (label .prefix)
  | .data => .pop 2 (label .restore) (label .bit) (label .bit)
  | .bit => .read (label (.store false)) (label (.store false)) (label (.store true))
  | .store b => .push 1 b (label .data)
  | .restore => .pop 1 (label .done) (label (.place false)) (label (.place true))
  | .place b => .push 0 b (label .restore)
  | .done => .halt

def program : Program := ⟨Fintype.card Q,4,label .prefix,fun pc => code ((Fintype.equivFin Q).symm pc)⟩
def config (q : Q) (m : Memory 4) : Config program := ⟨some (label q),m⟩
def exec (t : ℕ) (cfg : Config program) : Config program :=
  (List.replicate t false).foldl (fun cfg b => step program b cfg) cfg

theorem exec_add (s t : ℕ) (cfg : Config program) : exec (s+t) cfg=exec t (exec s cfg) := by
  simp only [exec,List.replicate_add,List.foldl_append]

@[simp] theorem exec_zero (cfg : Config program) : exec 0 cfg=cfg := rfl
@[simp] theorem exec_one (cfg : Config program) : exec 1 cfg=step program false cfg := rfl

theorem one_step (q : Q) (m : Memory 4) (coin : Bool) :
    step program coin (config q m)=⟨(effect (code q) coin m).1,(effect (code q) coin m).2⟩ := by
  simp [step,program,config,label]

theorem prefix_zero (m : Memory 4) (rest : List Bool) (h : m.input=false::rest) :
    exec 1 (config .prefix m)=config .data m.read := by
  rw [exec_one,one_step]
  simp [code,effect,branch,h,config]
  rfl

theorem prefix_one (m : Memory 4) (rest : List Bool) (h : m.input=true::rest) :
    exec 2 (config .prefix m)=config .prefix (m.read.push 2 false) := by
  change step program false (step program false (config .prefix m))=_
  rw [one_step]
  have he : (⟨(effect (code .prefix) false m).1,(effect (code .prefix) false m).2⟩ : Config program)=config .count m.read := by
    simp [code,effect,branch,h,config]; rfl
  rw [he,one_step]
  rfl

def prefixMemory : ℕ→Memory 4→Memory 4
  | 0,m => m.read
  | n+1,m => prefixMemory n (m.read.push 2 false)

theorem prefix_run (n : ℕ) (m : Memory 4) (rest : List Bool)
    (hi : m.input=List.replicate n true++false::rest) :
    exec (2*n+1) (config .prefix m)=config .data (prefixMemory n m) := by
  induction n generalizing m with
  | zero => exact prefix_zero m rest hi
  | succ n ih =>
    have he : 2*(n+1)+1=2+(2*n+1) := by omega
    rw [he,exec_add,prefix_one m _ hi,ih]
    · rfl
    · simp [Memory.push,Memory.read,hi,List.replicate_succ]

theorem prefixMemory_fields (n : ℕ) (m : Memory 4) (rest : List Bool)
    (hi : m.input=List.replicate n true++false::rest) :
    (prefixMemory n m).input=rest ∧
    (prefixMemory n m).stack 0=m.stack 0 ∧
    (prefixMemory n m).stack 1=m.stack 1 ∧
    (prefixMemory n m).stack 2=List.replicate n false++m.stack 2 ∧
    (prefixMemory n m).stack 3=m.stack 3 ∧
    (prefixMemory n m).outputRev=m.outputRev := by
  induction n generalizing m with
  | zero => simp [prefixMemory,Memory.read,hi]
  | succ n ih =>
    have hh := ih (m.read.push 2 false) (by simp [Memory.push,Memory.read,hi,List.replicate_succ])
    have he : List.replicate n false++false::m.stack 2=List.replicate (n+1) false++m.stack 2 := by
      rw [show List.replicate (n+1) false=List.replicate n false++[false] by rw [List.replicate_add]; rfl,List.append_assoc]; rfl
    simpa [prefixMemory,Memory.push,Memory.read,he] using hh

def digitMemory (b : Bool) (m : Memory 4) : Memory 4 := ((m.pop 2).read).push 1 b

theorem digit_run (b : Bool) (m : Memory 4) (rest count : List Bool)
    (hi : m.input=b::rest) (h2 : m.stack 2=false::count) :
    exec 3 (config .data m)=config .data (digitMemory b m) := by
  change step program false (step program false (step program false (config .data m)))=_
  rw [one_step]
  have he : (⟨(effect (code .data) false m).1,(effect (code .data) false m).2⟩ : Config program)=config .bit (m.pop 2) := by
    simp [code,effect,branch,h2,config]; rfl
  rw [he,one_step]
  have he' : (⟨(effect (code .bit) false (m.pop 2)).1,(effect (code .bit) false (m.pop 2)).2⟩ : Config program)=config (.store b) (m.pop 2).read := by
    cases b <;> simp [code,effect,branch,hi,config,Memory.pop] <;> rfl
  rw [he',one_step]
  rfl

def dataMemory : List Bool→Memory 4→Memory 4
  | [],m => m
  | b::bs,m => dataMemory bs (digitMemory b m)

theorem data_run (bs : List Bool) (m : Memory 4) (rest : List Bool)
    (hi : m.input=bs++rest) (h2 : m.stack 2=List.replicate bs.length false) :
    exec (3*bs.length) (config .data m)=config .data (dataMemory bs m) := by
  induction bs generalizing m with
  | nil => rfl
  | cons b bs ih =>
    have he : 3*(b::bs).length=3+3*bs.length := by simp; omega
    rw [he,exec_add,digit_run b m _ _ hi h2,ih]
    · rfl
    · simp [digitMemory,Memory.push,Memory.read,Memory.pop,hi]
    · simp [digitMemory,Memory.push,Memory.read,Memory.pop,h2,List.replicate_succ]

theorem dataMemory_fields (bs : List Bool) (m : Memory 4) (rest : List Bool)
    (hi : m.input=bs++rest) (h2 : m.stack 2=List.replicate bs.length false) :
    (dataMemory bs m).input=rest ∧
    (dataMemory bs m).stack 0=m.stack 0 ∧
    (dataMemory bs m).stack 1=bs.reverse++m.stack 1 ∧
    (dataMemory bs m).stack 2=[] ∧
    (dataMemory bs m).stack 3=m.stack 3 ∧
    (dataMemory bs m).outputRev=m.outputRev := by
  induction bs generalizing m with
  | nil => exact ⟨hi,rfl,rfl,h2,rfl,rfl⟩
  | cons b bs ih =>
    have hh := ih (digitMemory b m) (by simp [digitMemory,Memory.push,Memory.read,Memory.pop,hi])
      (by simp [digitMemory,Memory.push,Memory.read,Memory.pop,h2,List.replicate_succ])
    simpa [dataMemory,digitMemory,Memory.push,Memory.read,Memory.pop,List.reverse_cons,List.append_assoc] using hh

end
end Contingency.BitModel.StackCode.ParseNat

end

end OAI
