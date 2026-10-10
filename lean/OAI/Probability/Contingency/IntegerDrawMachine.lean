import Mathlib
import OAI.Probability.Contingency.IntegerDraw

namespace OAI

/-! Integer Draw Machine. -/

noncomputable section

open scoped BigOperators
namespace Contingency.BitModel.StackCode.IntegerDraw
open BinaryTrial
noncomputable section

structure RejectFrame (bound : List Bool) where
  draw : List Digit
  bound_eq : draw.map Digit.bound=bound
  clear : List Bool
  clear_length : clear.length=draw.length
  restore : List Pair
  restore_eq : restore.map Pair.bit=bound.reverse
  a : Bool
  b : Bool
  c : Bool
  d : Bool

def RejectFrame.coins {B : List Bool} (f : RejectFrame B) : List Bool :=
  rejectBits f.draw f.clear f.restore f.a f.b f.c f.d

def RejectFrame.rejected {B : List Bool} (f : RejectFrame B) : Prop :=
  ¬beValue (f.draw.map Digit.coin)≤beValue B

def RejectFrame.next {B : List Bool} (f : RejectFrame B) (m : Memory 4) : Memory 4 :=
  rejectMemory f.draw f.clear f.restore m

theorem RejectFrame.run {B : List Bool} (f : RejectFrame B) (m : Memory 4)
    (hm0 : m.stack 0=B) (hm1 : m.stack 1=[]) (hm2 : m.stack 2=[]) (hf : f.rejected) :
    f.coins.foldl (fun c b => step program b c) (config (.start .eq) m)=
      config (.start .eq) (f.next m) := by
  exact reject_run _ _ _ _ (hm0.trans f.bound_eq.symm) hm1 hm2 f.clear_length
    (by rw [f.bound_eq,f.restore_eq]) (by simpa [RejectFrame.rejected,f.bound_eq] using hf) _ _ _ _

theorem RejectFrame.invariant {B : List Bool} (f : RejectFrame B) (m : Memory 4)
    (hm0 : m.stack 0=B) (hm1 : m.stack 1=[]) (hm2 : m.stack 2=[]) :
    (f.next m).stack 0=B ∧ (f.next m).stack 1=[] ∧ (f.next m).stack 2=[] ∧
      (f.next m).outputRev=m.outputRev := by
  have hh := reject_stacks _ _ _ m (hm0.trans f.bound_eq.symm) hm1 hm2 f.clear_length
    (by rw [f.bound_eq,f.restore_eq])
  simpa [RejectFrame.next,hm0] using hh

theorem RejectFrame.length {B : List Bool} (f : RejectFrame B) : f.coins.length=7*B.length+4 := by
  have hl := congrArg List.length f.bound_eq
  simp only [List.length_map] at hl
  simpa [RejectFrame.coins,hl] using reject_length f.draw f.clear f.restore f.clear_length
    (by rw [f.bound_eq,f.restore_eq]) f.a f.b f.c f.d

def rejectedMemory {B : List Bool} (fs : List (RejectFrame B)) (m : Memory 4) : Memory 4 :=
  fs.foldl (fun m f => f.next m) m

theorem rejected_run {B : List Bool} (fs : List (RejectFrame B)) (m : Memory 4)
    (hm0 : m.stack 0=B) (hm1 : m.stack 1=[]) (hm2 : m.stack 2=[])
    (hf : ∀ f∈fs,f.rejected) :
    (fs.flatMap RejectFrame.coins).foldl (fun c b => step program b c) (config (.start .eq) m)=
      config (.start .eq) (rejectedMemory fs m) := by
  induction fs generalizing m with
  | nil => rfl
  | cons f fs ih =>
    have hi := f.invariant m hm0 hm1 hm2
    simp only [List.flatMap_cons,List.foldl_append]
    rw [f.run m hm0 hm1 hm2 (hf f (by simp)),ih _ hi.1 hi.2.1 hi.2.2.1]
    · rfl
    · intro g hg
      exact hf g (by simp [hg])

theorem rejected_invariant {B : List Bool} (fs : List (RejectFrame B)) (m : Memory 4)
    (hm0 : m.stack 0=B) (hm1 : m.stack 1=[]) (hm2 : m.stack 2=[]) :
    (rejectedMemory fs m).stack 0=B ∧ (rejectedMemory fs m).stack 1=[] ∧
      (rejectedMemory fs m).stack 2=[] ∧ (rejectedMemory fs m).outputRev=m.outputRev := by
  induction fs generalizing m with
  | nil => exact ⟨hm0,hm1,hm2,rfl⟩
  | cons f fs ih =>
    have hi := f.invariant m hm0 hm1 hm2
    have hs := ih _ hi.1 hi.2.1 hi.2.2.1
    exact ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.trans hi.2.2.2⟩

theorem rejected_length {B : List Bool} (fs : List (RejectFrame B)) :
    (fs.flatMap RejectFrame.coins).length=fs.length*(7*B.length+4) := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    simp only [List.flatMap_cons,List.length_append,f.length,ih,List.length_cons,Nat.add_mul]
    omega

structure AcceptFrame (bound : List Bool) where
  draw : List Digit
  bound_eq : draw.map Digit.bound=bound
  rev : List Pair
  rev_eq : rev.map Pair.bit=(draw.map Digit.coin).reverse
  out : List Pair
  out_eq : out.map Pair.bit=draw.map Digit.coin
  a : Bool
  b : Bool
  c : Bool
  d : Bool
  e : Bool

def AcceptFrame.coins {B : List Bool} (f : AcceptFrame B) : List Bool :=
  successBits f.draw f.rev f.out f.a f.b f.c f.d f.e

def AcceptFrame.accepted {B : List Bool} (f : AcceptFrame B) : Prop :=
  beValue (f.draw.map Digit.coin)≤beValue B

def AcceptFrame.next {B : List Bool} (f : AcceptFrame B) (m : Memory 4) : Memory 4 :=
  successMemory f.draw f.rev f.out m

theorem AcceptFrame.run {B : List Bool} (f : AcceptFrame B) (m : Memory 4)
    (hm0 : m.stack 0=B) (hm1 : m.stack 1=[]) (hf : f.accepted) :
    f.coins.foldl (fun c b => step program b c) (config (.start .eq) m)=⟨none,f.next m⟩ := by
  exact success_run _ _ _ _ (hm0.trans f.bound_eq.symm) hm1 f.rev_eq f.out_eq
    (by simpa [AcceptFrame.accepted,f.bound_eq] using hf) _ _ _ _ _

theorem AcceptFrame.output {B : List Bool} (f : AcceptFrame B) (m : Memory 4)
    (hm0 : m.stack 0=B) (hm1 : m.stack 1=[]) :
    (f.next m).outputRev.reverse=m.outputRev.reverse++f.draw.map Digit.coin :=
  success_output _ _ _ _ (hm0.trans f.bound_eq.symm) hm1 f.rev_eq f.out_eq

theorem AcceptFrame.length {B : List Bool} (f : AcceptFrame B) : f.coins.length=8*B.length+5 := by
  have hl := congrArg List.length f.bound_eq
  simp only [List.length_map] at hl
  simpa [AcceptFrame.coins,hl] using success_length f.draw f.rev f.out f.rev_eq f.out_eq f.a f.b f.c f.d f.e

structure PrepareFrame (bound : List Bool) where
  load : List Pair
  load_eq : load.map Pair.bit=bound
  restore : List Pair
  restore_eq : restore.map Pair.bit=bound.reverse
  a : Bool
  b : Bool

def PrepareFrame.coins {B : List Bool} (f : PrepareFrame B) : List Bool :=
  prepareBits f.load f.restore f.a f.b

def PrepareFrame.prepared {B : List Bool} (f : PrepareFrame B) : Memory 4 :=
  prepareMemory f.load f.restore (initial program B).memory

theorem PrepareFrame.run {B : List Bool} (f : PrepareFrame B) :
    f.coins.foldl (fun c b => step program b c) (initial program B)=
      config (.start .eq) f.prepared := by
  have hh := prepare_run f.load f.restore (initial program B).memory
    f.load_eq.symm rfl (by rw [f.load_eq,f.restore_eq]) f.a f.b
  exact hh

theorem PrepareFrame.invariant {B : List Bool} (f : PrepareFrame B) :
    f.prepared.stack 0=B ∧ f.prepared.stack 1=[] ∧ f.prepared.stack 2=[] ∧ f.prepared.outputRev=[] := by
  exact prepare_stacks f.load f.restore (initial program B).memory f.load_eq.symm rfl rfl
    (by rw [f.load_eq,f.restore_eq])

theorem PrepareFrame.length {B : List Bool} (f : PrepareFrame B) : f.coins.length=4*B.length+2 := by
  have hl := congrArg List.length f.load_eq
  simp only [List.length_map] at hl
  simpa [PrepareFrame.coins,hl] using prepare_length f.load f.restore
    (by rw [f.load_eq,f.restore_eq]) f.a f.b

def executionBits {B : List Bool} (p : PrepareFrame B) (fs : List (RejectFrame B)) (a : AcceptFrame B) : List Bool :=
  p.coins ++ fs.flatMap RejectFrame.coins ++ a.coins

theorem execution_run {B : List Bool} (p : PrepareFrame B) (fs : List (RejectFrame B)) (a : AcceptFrame B)
    (hf : ∀ f∈fs,f.rejected) (ha : a.accepted) :
    let result := (executionBits p fs a).foldl (fun c b => step program b c) (initial program B)
    result.state=none ∧ result.memory.outputRev.reverse=a.draw.map Digit.coin := by
  have hi := p.invariant
  have hj := rejected_invariant fs p.prepared hi.1 hi.2.1 hi.2.2.1
  dsimp only
  simp only [executionBits,List.foldl_append]
  rw [p.run,rejected_run fs _ hi.1 hi.2.1 hi.2.2.1 hf,a.run _ hj.1 hj.2.1 ha]
  constructor
  · rfl
  · rw [a.output _ hj.1 hj.2.1,hj.2.2.2,hi.2.2.2]
    rfl

theorem execution_length {B : List Bool} (p : PrepareFrame B) (fs : List (RejectFrame B)) (a : AcceptFrame B) :
    (executionBits p fs a).length=12*B.length+7+fs.length*(7*B.length+4) := by
  simp only [executionBits,List.length_append,p.length,rejected_length,a.length]
  omega

 

def machine : Machine := compile program

def pairedBits (ps : List (Bool×Bool)) : List Bool := ps.flatMap (fun p => [p.1,p.2])

theorem compiled_execution {B : List Bool} (p : PrepareFrame B) (fs : List (RejectFrame B)) (a : AcceptFrame B)
    (hf : ∀ f∈fs,f.rejected) (ha : a.accepted) (ps : List (Bool×Bool))
    (hp : ps.map Prod.snd=executionBits p fs a) :
    let result := (pairedBits ps).foldl (fun c b => machine.step b c) (machine.initial B)
    result.state=none ∧ result.outputRev.reverse=a.draw.map Digit.coin := by
  have hh := execution_run p fs a hf ha
  dsimp only [machine,pairedBits]
  rw [← initial_eq,fold_pairs]
  have hm := List.foldl_map (f:=Prod.snd) (g:=fun c b => step program b c) (l:=ps) (init:=initial program B)
  rw [hp] at hm
  rw [← hm]
  simpa only [encode_halt,encode_output] using hh

theorem pairedBits_length (ps : List (Bool×Bool)) : (pairedBits ps).length=2*ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pairedBits,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at ih ⊢
    omega

theorem compiled_length {B : List Bool} (p : PrepareFrame B) (fs : List (RejectFrame B)) (a : AcceptFrame B)
    (ps : List (Bool×Bool)) (hp : ps.map Prod.snd=executionBits p fs a) :
    (pairedBits ps).length=2*(12*B.length+7+fs.length*(7*B.length+4)) := by
  have hh := congrArg List.length hp
  simp only [List.length_map,execution_length] at hh
  rw [pairedBits_length,hh]

end
end Contingency.BitModel.StackCode.IntegerDraw

 

 

 

namespace Contingency.BitModel.StackCode.IntegerDraw
open BinaryTrial
noncomputable section

def trace (f : ℕ→Bool) (s n : ℕ) : List Bool := List.ofFn (fun i : Fin n => f (s+i))

@[simp] theorem trace_length (f : ℕ→Bool) (s n : ℕ) : (trace f s n).length=n := by simp [trace]

theorem trace_append (f : ℕ→Bool) (s a b : ℕ) :
    trace f s a ++ trace f (s+a) b=trace f s (a+b) := by
  unfold trace
  rw [List.ofFn_add]
  simp [Nat.add_assoc]

@[simp] theorem trace_one (f : ℕ→Bool) (s : ℕ) : trace f s 1=[f s] := by simp [trace,List.ofFn_succ]
@[simp] theorem trace_two (f : ℕ→Bool) (s : ℕ) : trace f s 2=[f s,f (s+1)] := by simp [trace,List.ofFn_succ]

def makePairs (xs : List Bool) (f : ℕ→Bool) (s : ℕ) : List Pair :=
  List.ofFn fun i : Fin xs.length => ⟨xs.get i,f (s+i*2),f (s+i*2+1)⟩

@[simp] theorem makePairs_bits (xs : List Bool) (f : ℕ→Bool) (s : ℕ) :
    (makePairs xs f s).map Pair.bit=xs := by simp [makePairs,Function.comp_def]

@[simp] theorem makePairs_length (xs : List Bool) (f : ℕ→Bool) (s : ℕ) :
    (makePairs xs f s).length=xs.length := by simp [makePairs]

theorem makePairs_coins (xs : List Bool) (f : ℕ→Bool) (s : ℕ) :
    (makePairs xs f s).flatMap pairBits=trace f s (xs.length*2) := by
  unfold makePairs trace
  rw [List.ofFn_mul,List.flatMap_def,List.map_ofFn]
  congr 1

def streamDigits (B : List Bool) (f : ℕ→Bool) (s : ℕ) : List Digit :=
  digits B.get (fun i => f (s+i))

@[simp] theorem streamDigits_bound (B : List Bool) (f : ℕ→Bool) (s : ℕ) :
    (streamDigits B f s).map Digit.bound=B := by simp [streamDigits,List.ofFn_get]
@[simp] theorem streamDigits_length (B : List Bool) (f : ℕ→Bool) (s : ℕ) :
    (streamDigits B f s).length=B.length := by simp [streamDigits]

theorem streamDigits_coins (B : List Bool) (f : ℕ→Bool) (s : ℕ) :
    (streamDigits B f s).flatMap bits=trace f s (B.length*4) := by
  exact digits_bits B.get (fun i => f (s+i))

def streamPrepare (B : List Bool) (f : ℕ→Bool) : PrepareFrame B where
  load := makePairs B f 0
  load_eq := makePairs_bits _ _ _
  restore := makePairs B.reverse f (B.length*2+1)
  restore_eq := makePairs_bits _ _ _
  a := f (B.length*2)
  b := f (B.length*2+1+B.length*2)

theorem streamPrepare_coins (B : List Bool) (f : ℕ→Bool) :
    (streamPrepare B f).coins=trace f 0 (4*B.length+2) := by
  unfold PrepareFrame.coins prepareBits streamPrepare
  rw [makePairs_coins,makePairs_coins]
  simp only [List.length_reverse]
  rw [← trace_one f (B.length*2),← trace_one f (B.length*2+1+B.length*2)]
  rw [show trace f 0 (B.length*2) ++ trace f (B.length*2) 1 =
    trace f 0 (B.length*2+1) by simpa using trace_append f 0 (B.length*2) 1]
  rw [show trace f 0 (B.length*2+1) ++ trace f (B.length*2+1) (B.length*2)=
    trace f 0 (B.length*2+1+B.length*2) by simpa using trace_append f 0 (B.length*2+1) (B.length*2)]
  rw [show trace f 0 (B.length*2+1+B.length*2) ++
    trace f (B.length*2+1+B.length*2) 1=trace f 0 (B.length*2+1+B.length*2+1) by
    simpa using trace_append f 0 (B.length*2+1+B.length*2) 1]
  congr 1
  omega

def streamReject (B : List Bool) (f : ℕ→Bool) (s : ℕ) : RejectFrame B where
  draw := streamDigits B f s
  bound_eq := streamDigits_bound _ _ _
  clear := trace f (s+B.length*4+2) B.length
  clear_length := by simp
  restore := makePairs B.reverse f (s+B.length*4+2+B.length+1)
  restore_eq := makePairs_bits _ _ _
  a := f (s+B.length*4)
  b := f (s+B.length*4+1)
  c := f (s+B.length*4+2+B.length)
  d := f (s+B.length*4+2+B.length+1+B.length*2)

theorem streamReject_coins (B : List Bool) (f : ℕ→Bool) (s : ℕ) :
    (streamReject B f s).coins=trace f s (7*B.length+4) := by
  unfold RejectFrame.coins rejectBits streamReject
  rw [streamDigits_coins,makePairs_coins]
  simp only [List.length_reverse]
  rw [← trace_two,← trace_one f (s+B.length*4+2+B.length),
    ← trace_one f (s+B.length*4+2+B.length+1+B.length*2)]
  simp only [Nat.add_assoc,trace_append]
  congr 1
  omega

def streamAccept (B : List Bool) (f : ℕ→Bool) (s : ℕ) : AcceptFrame B where
  draw := streamDigits B f s
  bound_eq := streamDigits_bound _ _ _
  rev := makePairs ((streamDigits B f s).map Digit.coin).reverse f (s+B.length*4+2)
  rev_eq := makePairs_bits _ _ _
  out := makePairs ((streamDigits B f s).map Digit.coin) f (s+B.length*4+2+B.length*2+1)
  out_eq := makePairs_bits _ _ _
  a := f (s+B.length*4)
  b := f (s+B.length*4+1)
  c := f (s+B.length*4+2+B.length*2)
  d := f (s+B.length*4+2+B.length*2+1+B.length*2)
  e := f (s+B.length*4+2+B.length*2+1+B.length*2+1)

theorem streamAccept_coins (B : List Bool) (f : ℕ→Bool) (s : ℕ) :
    (streamAccept B f s).coins=trace f s (8*B.length+5) := by
  unfold AcceptFrame.coins successBits streamAccept
  rw [streamDigits_coins,makePairs_coins,makePairs_coins]
  simp only [List.length_reverse,List.length_map,streamDigits_length]
  rw [← trace_two f (s+B.length*4),← trace_one f (s+B.length*4+2+B.length*2),
    ← trace_two f (s+B.length*4+2+B.length*2+1+B.length*2)]
  simp only [Nat.add_assoc,trace_append]
  congr 1
  omega

end
end Contingency.BitModel.StackCode.IntegerDraw

 

 

 

namespace Contingency.BitModel.StackCode.IntegerDraw
open BinaryTrial
noncomputable section

def prepTime (B : List Bool) : ℕ := 4*B.length+2
def retryTime (B : List Bool) : ℕ := 7*B.length+4
def successTime (B : List Bool) : ℕ := 8*B.length+5
def startTime (B : List Bool) (j : ℕ) : ℕ := prepTime B+j*retryTime B

def candidate (B : List Bool) (f : ℕ→Bool) (j : ℕ) : List Bool :=
  (streamDigits B f (startTime B j)).map Digit.coin

def accepted (B : List Bool) (f : ℕ→Bool) (j : ℕ) : Prop := beValue (candidate B f j)≤beValue B

def retries (B : List Bool) (f : ℕ→Bool) (j : ℕ) : List (RejectFrame B) :=
  List.ofFn fun i : Fin j => streamReject B f (startTime B i)

@[simp] theorem retries_length (B : List Bool) (f : ℕ→Bool) (j : ℕ) : (retries B f j).length=j := by simp [retries]

theorem retries_coins (B : List Bool) (f : ℕ→Bool) (j : ℕ) :
    ((retries B f j).flatMap RejectFrame.coins)=trace f (prepTime B) (j*retryTime B) := by
  induction j with
  | zero => simp [retries,trace]
  | succ j ih =>
    simp only [retries,List.ofFn_succ',List.concat_eq_append,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    change (retries B f j).flatMap RejectFrame.coins ++ (streamReject B f (startTime B j)).coins=_
    rw [ih,streamReject_coins]
    change trace f (prepTime B) (j*retryTime B) ++ trace f (prepTime B+j*retryTime B) (retryTime B)=_
    rw [trace_append,Nat.succ_mul]

theorem first_accept (B : List Bool) (f : ℕ→Bool) (j : ℕ)
    (hj : accepted B f j) (hp : ∀ i<j,¬accepted B f i) :
    let result := (trace f 0 (startTime B j+successTime B)).foldl (fun c b => step program b c) (initial program B)
    result.state=none ∧ result.memory.outputRev.reverse=candidate B f j := by
  have hr : ∀ a∈retries B f j,a.rejected := by
    intro a ha
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp ha
    subst a
    exact hp i i.isLt
  have hh := execution_run (streamPrepare B f) (retries B f j)
    (streamAccept B f (startTime B j)) hr hj
  have he : executionBits (streamPrepare B f) (retries B f j) (streamAccept B f (startTime B j))=
      trace f 0 (startTime B j+successTime B) := by
    unfold executionBits
    rw [streamPrepare_coins,retries_coins,streamAccept_coins]
    change trace f 0 (prepTime B) ++ trace f (prepTime B) (j*retryTime B) ++
      trace f (prepTime B+j*retryTime B) (successTime B)=_
    rw [show trace f 0 (prepTime B) ++ trace f (prepTime B) (j*retryTime B)=
      trace f 0 (prepTime B+j*retryTime B) by simpa using trace_append f 0 (prepTime B) (j*retryTime B)]
    simpa [startTime] using trace_append f 0 (prepTime B+j*retryTime B) (successTime B)
  rw [he] at hh
  exact hh

 theorem halted_fold (P : Program) (bs : List Bool) (m : Memory P.work) :
    bs.foldl (fun c b => step P b c) ⟨none,m⟩=⟨none,m⟩ := by
  induction bs with
  | nil => rfl
  | cons b bs ih => exact ih

 theorem first_accept_later (B : List Bool) (f : ℕ→Bool) (j t : ℕ)
    (hj : accepted B f j) (hp : ∀ i<j,¬accepted B f i) (ht : startTime B j+successTime B≤t) :
    let result := (trace f 0 t).foldl (fun c b => step program b c) (initial program B)
    result.state=none ∧ result.memory.outputRev.reverse=candidate B f j := by
  have hh := first_accept B f j hj hp
  let T := startTime B j+successTime B
  have he : trace f 0 t=trace f 0 T ++ trace f T (t-T) := by
    have := trace_append f 0 T (t-T)
    have hT : T+(t-T)=t := by omega
    simpa only [Nat.zero_add,hT] using this.symm
  rw [he,List.foldl_append]
  generalize hc : (trace f 0 T).foldl (fun c b => step program b c) (initial program B)=c at hh ⊢
  rcases c with ⟨s,m⟩
  change s=none ∧ _ at hh
  rcases hh with ⟨rfl,ho⟩
  dsimp only
  rw [halted_fold]
  exact ⟨rfl,ho⟩

 theorem accepts_halt (B : List Bool) (f : ℕ→Bool) (k t : ℕ)
    (ha : ∃ j<k,accepted B f j) (ht : startTime B k+successTime B≤t) :
    ((trace f 0 t).foldl (fun c b => step program b c) (initial program B)).state=none := by
  classical
  let j := Nat.find ha
  have hj := Nat.find_spec ha
  have hp : ∀ i<j,¬accepted B f i := by
    intro i hi hai
    have := Nat.find_min' ha (show i<k ∧ accepted B f i from ⟨lt_trans hi hj.1,hai⟩)
    omega
  exact (first_accept_later B f j t hj.2 hp (by
    dsimp [startTime] at ht ⊢
    exact le_trans (Nat.add_le_add_right (Nat.add_le_add_left
      (Nat.mul_le_mul_right (retryTime B) (Nat.le_of_lt hj.1)) _) _) ht)).1

end
end Contingency.BitModel.StackCode.IntegerDraw

 

 

 

open scoped BigOperators
namespace Contingency.BitModel.CoordinateLaw
noncomputable section
open Function

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def indexEquiv (e : α→β) (he : Injective e) : α ⊕ {b : β // b∉Set.range e} ≃ β := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective e he) (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range e))

omit [Fintype β] [DecidableEq α] in
@[simp] theorem indexEquiv_left (e : α→β) (he : Injective e) (a : α) : indexEquiv e he (.inl a)=e a := rfl

def split (e : α→β) (he : Injective e) :
    (β→Bool) ≃ (α→Bool)×({b : β // b∉Set.range e}→Bool) :=
  ((indexEquiv e he).symm.arrowCongr (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

omit [Fintype β] [DecidableEq α] in
@[simp] theorem split_left (e : α→β) (he : Injective e) (f : β→Bool) :
    (split e he f).1=f∘e := rfl

theorem count_restrict (e : α→β) (he : Injective e) (p : (α→Bool)→Prop) [DecidablePred p] :
    (Finset.univ.filter fun f : β→Bool => p (f∘e)).card=
      2^(Nat.card {b : β // b∉Set.range e})*(Finset.univ.filter p).card := by
  classical
  simp only [Finset.card_filter]
  change (∑ f,if p ((split e he f).1) then 1 else 0)=_
  rw [(split e he).sum_comp (fun ab => if p ab.1 then (1:ℕ) else 0),Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bs _
  by_cases hp : p bs <;> simp [hp,Nat.card_eq_fintype_card]

omit [DecidableEq α] in
theorem cardinal_split (e : α→β) (he : Injective e) :
    Fintype.card β=Fintype.card α+Nat.card {b : β // b∉Set.range e} := by
  classical
  simpa [Nat.card_eq_fintype_card] using (Fintype.card_congr (indexEquiv e he)).symm

theorem probability_restrict (e : α→β) (he : Injective e) (p : (α→Bool)→Prop) [DecidablePred p] :
    ((Finset.univ.filter fun f : β→Bool => p (f∘e)).card:ℝ)/2^(Fintype.card β)=
      ((Finset.univ.filter p).card:ℝ)/2^(Fintype.card α) := by
  rw [count_restrict e he p,cardinal_split e he]
  push_cast
  rw [pow_add]
  field_simp

theorem count_all {γ : Type*} [Fintype γ] (k : ℕ) (p : γ→Prop) [DecidablePred p] :
    (Finset.univ.filter fun f : Fin k→γ => ∀ i,p (f i)).card=(Finset.univ.filter p).card^k := by
  classical
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (Equiv.subtypePiEquivPi (p:=fun (_ : Fin k) (v : γ) => p v))]
  simp [Fintype.card_subtype]

end
end Contingency.BitModel.CoordinateLaw

 

 

 

open Filter
namespace Contingency.BitModel.StackCode

 theorem prepare_observe (P : Program) (c : Config P) (b : Bool) :
    ((compile P).step b (encode P c)).state=none ↔ c.state=none := by
  rcases c with ⟨s,m⟩
  cases s with
  | none =>
    dsimp only [encode,compile]
    simp [Machine.step]
  | some pc =>
    dsimp only [Machine.step,encode]
    dsimp only [compile]
    cases h : P.code pc <;> simp [first,prepare,h,active,preserved]

 theorem prepare_output (P : Program) (c : Config P) (b : Bool) :
    ((compile P).step b (encode P c)).outputRev=c.memory.outputRev := by
  rcases c with ⟨s,m⟩
  cases s with
  | none =>
    dsimp only [encode,compile]
    simp [Machine.step]
  | some pc =>
    dsimp only [Machine.step,encode]
    dsimp only [compile]
    cases h : P.code pc <;> simp [first,prepare,h,active,preserved]

 theorem machine_run_succ (M : Machine) (xs : List Bool) {t : ℕ} (coins : Fin (t+1)→Bool) :
    M.run xs coins=M.step (coins (Fin.last t)) (M.run xs (fun i : Fin t => coins i.castSucc)) := by
  unfold Machine.run
  rw [List.ofFn_succ',List.concat_eq_append,List.foldl_append]
  rfl

 def coinLast (t : ℕ) : (Fin (t+1)→Bool) ≃ (Fin t→Bool)×Bool where
  toFun f := (fun i => f i.castSucc,f (Fin.last t))
  invFun p := Fin.lastCases p.2 p.1
  left_inv f := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv p := by rcases p with ⟨f,b⟩; simp

 theorem count_last (t : ℕ) (p : (Fin t→Bool)→Prop) [DecidablePred p] :
    (Finset.univ.filter fun c : Fin (t+1)→Bool => p (fun i => c i.castSucc)).card=
      2*(Finset.univ.filter p).card := by
  classical
  simp only [Finset.card_filter]
  change (∑ c,if p ((coinLast t c).1) then 1 else 0)=_
  rw [(coinLast t).sum_comp (fun ab => if p ab.1 then (1:ℕ) else 0),Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bs _
  by_cases hp : p bs <;> simp [hp]

 theorem mass_compile_odd (P : Program) (xs out : List Bool) (t : ℕ) :
    (compile P).mass xs out (t*2+1)=mass P xs out t := by
  classical
  unfold Machine.mass
  simp only [machine_run_succ,run_eq,prepare_observe,prepare_output]
  rw [count_last (t*2) (fun c => (run P xs (fun i => c (second i))).state=none ∧
    (run P xs (fun i => c (second i))).memory.outputRev.reverse=out)]
  rw [count_second t (fun c => (run P xs c).state=none ∧
    (run P xs c).memory.outputRev.reverse=out)]
  unfold mass
  push_cast
  rw [pow_succ,pow_mul,pow_two]
  field_simp

 theorem tail_compile_odd (P : Program) (xs : List Bool) (t : ℕ) :
    (compile P).tail xs (t*2+1)=tail P xs t := by
  classical
  unfold Machine.tail
  simp only [machine_run_succ,run_eq,ne_eq,prepare_observe]
  rw [count_last (t*2) (fun c => (run P xs (fun i => c (second i))).state≠none)]
  rw [count_second t (fun c => (run P xs c).state≠none)]
  unfold tail
  push_cast
  rw [pow_succ,pow_mul,pow_two]
  field_simp

 theorem mass_compile_all (P : Program) (xs out : List Bool) (t : ℕ) :
    (compile P).mass xs out t=mass P xs out (t/2) := by
  have hm := Nat.mod_lt t (by decide : 0<2)
  have hd := Nat.mod_add_div t 2
  rcases (show t%2=0 ∨ t%2=1 by omega) with h|h
  · have ht : t=t/2*2 := by omega
    conv_lhs => rw [ht]
    exact mass_compile P xs out (t/2)
  · have ht : t=t/2*2+1 := by omega
    conv_lhs => rw [ht]
    exact mass_compile_odd P xs out (t/2)

 theorem tail_compile_all (P : Program) (xs : List Bool) (t : ℕ) :
    (compile P).tail xs t=tail P xs (t/2) := by
  have hm := Nat.mod_lt t (by decide : 0<2)
  have hd := Nat.mod_add_div t 2
  rcases (show t%2=0 ∨ t%2=1 by omega) with h|h
  · have ht : t=t/2*2 := by omega
    conv_lhs => rw [ht]
    exact tail_compile P xs (t/2)
  · have ht : t=t/2*2+1 := by omega
    conv_lhs => rw [ht]
    exact tail_compile_odd P xs (t/2)

 theorem half_tendsto : Tendsto (fun t : ℕ => t/2) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (2*b)] with t ht
  omega

 theorem mass_limit_compile (P : Program) (xs out : List Bool) (r : ℝ)
    (h : Tendsto (mass P xs out) atTop (nhds r)) :
    Tendsto ((compile P).mass xs out) atTop (nhds r) := by
  simpa only [Function.comp_def,← mass_compile_all] using h.comp half_tendsto

 theorem tail_limit_compile (P : Program) (xs : List Bool) (r : ℝ)
    (h : Tendsto (tail P xs) atTop (nhds r)) :
    Tendsto ((compile P).tail xs) atTop (nhds r) := by
  simpa only [Function.comp_def,← tail_compile_all] using h.comp half_tendsto

 theorem tail_summable_compile (P : Program) (xs : List Bool) (h : Summable (tail P xs)) :
    Summable ((compile P).tail xs) := by
  apply Summable.even_add_odd
  · simpa only [Nat.mul_comm 2,tail_compile] using h
  · simpa only [Nat.mul_comm 2,tail_compile_odd] using h

 

 theorem expected_compile (P : Program) (xs : List Bool) (h : Summable (tail P xs)) :
    (∑' t,(compile P).tail xs t)=2*(∑' t,tail P xs t) := by
  have he : Summable (fun t => (compile P).tail xs (2*t)) := by
    simpa only [Nat.mul_comm 2,tail_compile] using h
  have ho : Summable (fun t => (compile P).tail xs (2*t+1)) := by
    simpa only [Nat.mul_comm 2,tail_compile_odd] using h
  rw [← tsum_even_add_odd he ho]
  simp only [Nat.mul_comm 2,tail_compile,tail_compile_odd]
  ring

end Contingency.BitModel.StackCode

end

end OAI
