import Mathlib
import OAI.Probability.Contingency.CompletionTranslation
import OAI.Probability.Contingency.StackCompiler

namespace OAI

/-! Integer Draw. -/

noncomputable section

open scoped BigOperators
namespace Contingency.BitModel.StackCode.IntegerDraw
open BinaryTrial
noncomputable section

inductive Q
  | read
  | store (b : Bool)
  | restore
  | restorePlace (b : Bool)
  | start (s : Cmp)
  | save (s : Cmp) (v : Bool)
  | choose (s : Cmp) (v : Bool)
  | place (s : Cmp) (v b : Bool)
  | decide (s : Cmp)
  | discard
  | reverseDraw
  | reversePlace (b : Bool)
  | output
  | emit (b : Bool)
  | halt
  deriving DecidableEq, Fintype

def label (q : Q) : Fin (Fintype.card Q) := Fintype.equivFin Q q

def code : Q → Op (Fintype.card Q) 4
  | .read => .read (label .restore) (label (.store false)) (label (.store true))
  | .store b => .push 2 b (label .read)
  | .restore => .pop 2 (label (.start .eq)) (label (.restorePlace false)) (label (.restorePlace true))
  | .restorePlace b => .push 0 b (label .restore)
  | .start s => .pop 0 (label (.decide s)) (label (.save s false)) (label (.save s true))
  | .save s v => .push 2 v (label (.choose s v))
  | .choose s v => .coin (label (.place s v false)) (label (.place s v true))
  | .place s v b => .push 1 b (label (.start (advance s v b)))
  | .decide s => .jump (label (if accept s then .reverseDraw else .discard))
  | .discard => .pop 1 (label .restore) (label .discard) (label .discard)
  | .reverseDraw => .pop 1 (label .output) (label (.reversePlace false)) (label (.reversePlace true))
  | .reversePlace b => .push 0 b (label .reverseDraw)
  | .output => .pop 0 (label .halt) (label (.emit false)) (label (.emit true))
  | .emit b => .emit b (label .output)
  | .halt => .halt

def program : Program := ⟨Fintype.card Q,4,label .read,fun pc => code ((Fintype.equivFin Q).symm pc)⟩

def config (q : Q) (m : Memory 4) : Config program := ⟨some (label q),m⟩

theorem one_step (q : Q) (m : Memory 4) (coin : Bool) :
    step program coin (config q m)=
      ⟨(effect (code q) coin m).1,(effect (code q) coin m).2⟩ := by
  simp [step,config,program,label]

theorem four_steps (s : Cmp) (m : Memory 4) (v b n₀ n₁ n₃ : Bool) (rest : List Bool)
    (hm : m.stack 0=v::rest) :
    [n₀,n₁,b,n₃].foldl (fun c z => step program z c) (config (.start s) m)=
      config (.start (advance s v b)) (digitMemory m v b) := by
  cases v <;> cases b <;>
    simp [List.foldl_cons,List.foldl_nil,code,effect,branch,hm,config,digitMemory,
      step,program,label]

theorem pass (ds : List Digit) (s : Cmp) (m : Memory 4)
    (hm : m.stack 0=ds.map Digit.bound) :
    (ds.flatMap bits).foldl (fun c b => step program b c) (config (.start s) m)=
      config (.start (wordCmp ds s)) (wordMemory ds m) := by
  induction ds generalizing s m with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.flatMap_cons,List.foldl_append]
    rw [show bits d=[d.noise₀,d.noise₁,d.coin,d.noise₃] from rfl]
    rw [four_steps s m d.bound d.coin d.noise₀ d.noise₁ d.noise₃ _ hm]
    rw [ih]
    · rfl
    · simp [hm]

theorem decision (s : Cmp) (m : Memory 4) (hn : m.stack 0=[]) (b₀ b₁ : Bool) :
    [b₀,b₁].foldl (fun c b => step program b c) (config (.start s) m)=
      config (if accept s then .reverseDraw else .discard) (m.pop 0) := by
  simp [List.foldl_cons,List.foldl_nil,step,program,label,config,code,effect,branch,hn]

 
structure Pair where
  bit : Bool
  noise₀ : Bool
  noise₁ : Bool

def pairBits (p : Pair) : List Bool := [p.noise₀,p.noise₁]

def moveMemory (m : Memory 4) (i j : Fin 4) (b : Bool) : Memory 4 := (m.pop i).push j b

@[simp] theorem move_from (m : Memory 4) (i j : Fin 4) (b : Bool) (h : i≠j) :
    (moveMemory m i j b).stack i=(m.stack i).tail := by
  simp [moveMemory,Memory.pop,Memory.push,h]
@[simp] theorem move_to (m : Memory 4) (i j : Fin 4) (b : Bool) (h : i≠j) :
    (moveMemory m i j b).stack j=b::m.stack j := by
  simp [moveMemory,Memory.pop,Memory.push,Ne.symm h]
@[simp] theorem move_other (m : Memory 4) (i j k : Fin 4) (b : Bool) (hi : k≠i) (hj : k≠j) :
    (moveMemory m i j b).stack k=m.stack k := by simp [moveMemory,Memory.pop,Memory.push,hi,hj]

def moveWord (ps : List Pair) (i j : Fin 4) (m : Memory 4) : Memory 4 :=
  ps.foldl (fun m p => moveMemory m i j p.bit) m

theorem moveWord_stacks (ps : List Pair) (i j : Fin 4) (m : Memory 4)
    (hij : i≠j) (hm : m.stack i=ps.map Pair.bit) :
    (moveWord ps i j m).stack i=[] ∧
    (moveWord ps i j m).stack j=(ps.map Pair.bit).reverse++m.stack j ∧
    (∀ k, k≠i → k≠j → (moveWord ps i j m).stack k=m.stack k) := by
  induction ps generalizing m with
  | nil => simp_all [moveWord]
  | cons p ps ih =>
    have ht : (moveMemory m i j p.bit).stack i=ps.map Pair.bit := by simp [hij,hm]
    have hs := ih (moveMemory m i j p.bit) ht
    refine ⟨hs.1,?_,?_⟩
    · simpa [moveWord,List.reverse_cons,List.append_assoc,hij] using hs.2.1
    · intro k hi hj
      exact (hs.2.2 k hi hj).trans (move_other m i j k p.bit hi hj)

theorem restore_two (m : Memory 4) (p : Pair) (rest : List Bool)
    (hm : m.stack 2=p.bit::rest) :
    (pairBits p).foldl (fun c b => step program b c) (config .restore m)=
      config .restore (moveMemory m 2 0 p.bit) := by
  cases p with
  | mk v b₀ b₁ => cases v <;>
    simp [pairBits,List.foldl_cons,List.foldl_nil,step,program,label,config,code,effect,branch,hm,moveMemory]

theorem restore_pass (ps : List Pair) (m : Memory 4) (hm : m.stack 2=ps.map Pair.bit) :
    (ps.flatMap pairBits).foldl (fun c b => step program b c) (config .restore m)=
      config .restore (moveWord ps 2 0 m) := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons,List.foldl_append]
    rw [restore_two m p _ hm,ih]
    · rfl
    · simp [hm]

theorem restore_finish (m : Memory 4) (hm : m.stack 2=[]) (b : Bool) :
    step program b (config .restore m)=config (.start .eq) (m.pop 2) := by
  rw [one_step]
  simp [code,effect,branch,hm,config]
  rfl

theorem reverse_two (m : Memory 4) (p : Pair) (rest : List Bool)
    (hm : m.stack 1=p.bit::rest) :
    (pairBits p).foldl (fun c b => step program b c) (config .reverseDraw m)=
      config .reverseDraw (moveMemory m 1 0 p.bit) := by
  cases p with
  | mk v b₀ b₁ => cases v <;>
    simp [pairBits,List.foldl_cons,List.foldl_nil,step,program,label,config,code,effect,branch,hm,moveMemory]

theorem reverse_pass (ps : List Pair) (m : Memory 4) (hm : m.stack 1=ps.map Pair.bit) :
    (ps.flatMap pairBits).foldl (fun c b => step program b c) (config .reverseDraw m)=
      config .reverseDraw (moveWord ps 1 0 m) := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons,List.foldl_append]
    rw [reverse_two m p _ hm,ih]
    · rfl
    · simp [hm]

theorem reverse_finish (m : Memory 4) (hm : m.stack 1=[]) (b : Bool) :
    step program b (config .reverseDraw m)=config .output (m.pop 1) := by
  rw [one_step]
  simp [code,effect,branch,hm,config]
  rfl

def emitMemory (m : Memory 4) (b : Bool) : Memory 4 :=
  {m.pop 0 with outputRev := b::m.outputRev}

def emitWord (ps : List Pair) (m : Memory 4) : Memory 4 :=
  ps.foldl (fun m p => emitMemory m p.bit) m

theorem emit_two (m : Memory 4) (p : Pair) (rest : List Bool)
    (hm : m.stack 0=p.bit::rest) :
    (pairBits p).foldl (fun c b => step program b c) (config .output m)=
      config .output (emitMemory m p.bit) := by
  cases p with
  | mk v b₀ b₁ => cases v <;>
    simp [pairBits,List.foldl_cons,List.foldl_nil,step,program,label,config,code,effect,branch,hm,emitMemory] <;> rfl

theorem emit_pass (ps : List Pair) (m : Memory 4) (hm : m.stack 0=ps.map Pair.bit) :
    (ps.flatMap pairBits).foldl (fun c b => step program b c) (config .output m)=
      config .output (emitWord ps m) := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons,List.foldl_append]
    rw [emit_two m p _ hm,ih]
    · rfl
    · simp [emitMemory,Memory.pop,hm]

theorem emitWord_stacks (ps : List Pair) (m : Memory 4) (hm : m.stack 0=ps.map Pair.bit) :
    (emitWord ps m).stack 0=[] ∧
    (emitWord ps m).outputRev=(ps.map Pair.bit).reverse++m.outputRev := by
  induction ps generalizing m with
  | nil => simp_all [emitWord]
  | cons p ps ih =>
    have ht : (emitMemory m p.bit).stack 0=ps.map Pair.bit := by simp [emitMemory,Memory.pop,hm]
    have hs := ih (emitMemory m p.bit) ht
    simpa [emitWord,emitMemory,List.reverse_cons,List.append_assoc] using hs

theorem emit_finish (m : Memory 4) (hm : m.stack 0=[]) (b₀ b₁ : Bool) :
    [b₀,b₁].foldl (fun c b => step program b c) (config .output m)=⟨none,m.pop 0⟩ := by
  simp [List.foldl_cons,List.foldl_nil,step,program,label,config,code,effect,branch,hm]

end
end Contingency.BitModel.StackCode.IntegerDraw

 

 

 

namespace Contingency.BitModel.StackCode.IntegerDraw
open BinaryTrial
noncomputable section

@[simp] theorem push_input (m : Memory 4) (i : Fin 4) (b : Bool) : (m.push i b).input=m.input := rfl
@[simp] theorem pop_input (m : Memory 4) (i : Fin 4) : (m.pop i).input=m.input := rfl
@[simp] theorem push_output (m : Memory 4) (i : Fin 4) (b : Bool) : (m.push i b).outputRev=m.outputRev := rfl
@[simp] theorem pop_output (m : Memory 4) (i : Fin 4) : (m.pop i).outputRev=m.outputRev := rfl
@[simp] theorem pop_stack (m : Memory 4) (i : Fin 4) : (m.pop i).stack i=(m.stack i).tail := by simp [Memory.pop]
@[simp] theorem pop_other (m : Memory 4) (i j : Fin 4) (h : i≠j) : (m.pop i).stack j=m.stack j := by simp [Memory.pop,Ne.symm h]
@[simp] theorem moveWord_output (ps : List Pair) (i j : Fin 4) (m : Memory 4) :
    (moveWord ps i j m).outputRev=m.outputRev := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih => exact ih (moveMemory m i j p.bit)
@[simp] theorem wordMemory_output (ds : List Digit) (m : Memory 4) :
    (wordMemory ds m).outputRev=m.outputRev := by
  induction ds generalizing m with
  | nil => rfl
  | cons d ds ih => exact ih (digitMemory m d.bound d.coin)

def loadMemory (m : Memory 4) (b : Bool) : Memory 4 := m.read.push 2 b

def loadWord (ps : List Pair) (m : Memory 4) : Memory 4 := ps.foldl (fun m p => loadMemory m p.bit) m

theorem load_two (m : Memory 4) (p : Pair) (rest : List Bool) (hm : m.input=p.bit::rest) :
    (pairBits p).foldl (fun c b => step program b c) (config .read m)=
      config .read (loadMemory m p.bit) := by
  cases p with
  | mk v b₀ b₁ => cases v <;>
    simp [pairBits,List.foldl_cons,List.foldl_nil,step,program,label,config,code,effect,branch,hm,loadMemory]

theorem load_pass (ps : List Pair) (m : Memory 4) (hm : m.input=ps.map Pair.bit) :
    (ps.flatMap pairBits).foldl (fun c b => step program b c) (config .read m)=
      config .read (loadWord ps m) := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons,List.foldl_append]
    rw [load_two m p _ hm,ih]
    · rfl
    · simp [loadMemory,Memory.read,hm]

theorem loadWord_stacks (ps : List Pair) (m : Memory 4) (hm : m.input=ps.map Pair.bit) :
    (loadWord ps m).input=[] ∧
    (loadWord ps m).stack 2=(ps.map Pair.bit).reverse++m.stack 2 ∧
    (∀ k, k≠2 → (loadWord ps m).stack k=m.stack k) ∧
    (loadWord ps m).outputRev=m.outputRev := by
  induction ps generalizing m with
  | nil => simp_all [loadWord]
  | cons p ps ih =>
    have ht : (loadMemory m p.bit).input=ps.map Pair.bit := by simp [loadMemory,Memory.read,hm]
    have hs := ih (loadMemory m p.bit) ht
    refine ⟨hs.1,?_,?_,hs.2.2.2⟩
    · simpa [loadWord,loadMemory,Memory.push,Memory.read,List.reverse_cons,List.append_assoc] using hs.2.1
    · intro k hk
      simpa [loadWord,loadMemory,Memory.push,Memory.read,hk] using hs.2.2.1 k hk

theorem load_finish (m : Memory 4) (hm : m.input=[]) (b : Bool) :
    step program b (config .read m)=config .restore m.read := by
  rw [one_step]
  simp [code,effect,branch,hm,config]
  rfl

def clearWord (bs : List Bool) (m : Memory 4) : Memory 4 := bs.foldl (fun m _ => m.pop 1) m

theorem discard_one (m : Memory 4) (v : Bool) (rest : List Bool) (hm : m.stack 1=v::rest) (b : Bool) :
    step program b (config .discard m)=config .discard (m.pop 1) := by
  rw [one_step]
  cases v <;> simp [code,effect,branch,hm,config] <;> rfl

theorem discard_pass (bs : List Bool) (m : Memory 4) (hm : (m.stack 1).length=bs.length) :
    bs.foldl (fun c b => step program b c) (config .discard m)=
      config .discard (clearWord bs m) := by
  induction bs generalizing m with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨v,rest,hs⟩ := List.exists_cons_of_length_pos (l:=m.stack 1) (by simp_all)
    simp only [List.foldl_cons]
    rw [discard_one m v rest hs b,ih]
    · rfl
    · simp [hs] at hm ⊢; omega

theorem clearWord_stacks (bs : List Bool) (m : Memory 4) (hm : (m.stack 1).length=bs.length) :
    (clearWord bs m).stack 1=[] ∧
    (∀ k, k≠1 → (clearWord bs m).stack k=m.stack k) ∧
    (clearWord bs m).outputRev=m.outputRev := by
  induction bs generalizing m with
  | nil => simpa [clearWord] using hm
  | cons b bs ih =>
    have ht : ((m.pop 1).stack 1).length=bs.length := by simp at hm; simp; omega
    have hs := ih (m.pop 1) ht
    refine ⟨hs.1,?_,hs.2.2⟩
    intro k hk
    simpa [clearWord,Memory.pop,hk] using hs.2.1 k hk

theorem discard_finish (m : Memory 4) (hm : m.stack 1=[]) (b : Bool) :
    step program b (config .discard m)=config .restore (m.pop 1) := by
  rw [one_step]
  simp [code,effect,branch,hm,config]
  rfl

theorem pairBits_length (ps : List Pair) : (ps.flatMap pairBits).length=2*ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [pairBits,ih]; omega

 
def successBits (ds : List Digit) (rev out : List Pair) (a b c d e : Bool) : List Bool :=
  ds.flatMap bits ++ [a,b] ++ rev.flatMap pairBits ++ [c] ++ out.flatMap pairBits ++ [d,e]

def successMemory (ds : List Digit) (rev out : List Pair) (m : Memory 4) : Memory 4 :=
  (emitWord out ((moveWord rev 1 0 ((wordMemory ds m).pop 0)).pop 1)).pop 0

theorem success_run (ds : List Digit) (rev out : List Pair) (m : Memory 4)
    (hm0 : m.stack 0=ds.map Digit.bound) (hm1 : m.stack 1=[])
    (hr : rev.map Pair.bit=(ds.map Digit.coin).reverse)
    (ho : out.map Pair.bit=ds.map Digit.coin)
    (ha : beValue (ds.map Digit.coin)≤beValue (ds.map Digit.bound))
    (a b c d e : Bool) :
    (successBits ds rev out a b c d e).foldl (fun c b => step program b c) (config (.start .eq) m)=
      ⟨none,successMemory ds rev out m⟩ := by
  have hs := pass_stacks ds m hm0
  have h0 : ((wordMemory ds m).pop 0).stack 0=[] := by simp [hs.1]
  have h1 : ((wordMemory ds m).pop 0).stack 1=rev.map Pair.bit := by simp [hs.2.1,hm1,hr]
  have hrst := moveWord_stacks rev 1 0 ((wordMemory ds m).pop 0) (by decide) h1
  have hr0 : ((moveWord rev 1 0 ((wordMemory ds m).pop 0)).pop 1).stack 0=out.map Pair.bit := by
    simp [hrst.2.1,hs.1,hr,ho]
  have he := emitWord_stacks out _ hr0
  unfold successBits
  simp only [List.foldl_append]
  rw [pass ds .eq m hm0,decision _ _ hs.1 a b,comparison_correct,ite_eq_left (by simpa using ha)]
  rw [reverse_pass rev _ h1]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [reverse_finish _ hrst.1 c,emit_pass out _ hr0]
  exact emit_finish _ he.1 d e

theorem success_output (ds : List Digit) (rev out : List Pair) (m : Memory 4)
    (hm0 : m.stack 0=ds.map Digit.bound) (hm1 : m.stack 1=[])
    (hr : rev.map Pair.bit=(ds.map Digit.coin).reverse)
    (ho : out.map Pair.bit=ds.map Digit.coin) :
    (successMemory ds rev out m).outputRev.reverse=m.outputRev.reverse++ds.map Digit.coin := by
  have hs := pass_stacks ds m hm0
  have h0 : ((wordMemory ds m).pop 0).stack 0=[] := by simp [hs.1]
  have h1 : ((wordMemory ds m).pop 0).stack 1=rev.map Pair.bit := by simp [hs.2.1,hm1,hr]
  have hrst := moveWord_stacks rev 1 0 ((wordMemory ds m).pop 0) (by decide) h1
  have hr0 : ((moveWord rev 1 0 ((wordMemory ds m).pop 0)).pop 1).stack 0=out.map Pair.bit := by
    simp [hrst.2.1,hs.1,hr,ho]
  have he := emitWord_stacks out _ hr0
  simp [successMemory,he.2,ho]

theorem success_length (ds : List Digit) (rev out : List Pair)
    (hr : rev.map Pair.bit=(ds.map Digit.coin).reverse)
    (ho : out.map Pair.bit=ds.map Digit.coin) (a b c d e : Bool) :
    (successBits ds rev out a b c d e).length=8*ds.length+5 := by
  have hlr := congrArg List.length hr
  have hlo := congrArg List.length ho
  simp only [List.length_map,List.length_reverse] at hlr hlo
  simp only [successBits,List.length_append,List.length_cons,List.length_nil,pass_length,pairBits_length,hlr,hlo]
  omega

end
end Contingency.BitModel.StackCode.IntegerDraw

 

 

 

namespace Contingency.BitModel.StackCode.IntegerDraw
open BinaryTrial
noncomputable section

def rejectBits (ds : List Digit) (clear : List Bool) (restore : List Pair) (a b c d : Bool) : List Bool :=
  ds.flatMap bits ++ [a,b] ++ clear ++ [c] ++ restore.flatMap pairBits ++ [d]

def rejectMemory (ds : List Digit) (clear : List Bool) (restore : List Pair) (m : Memory 4) : Memory 4 :=
  (moveWord restore 2 0 ((clearWord clear ((wordMemory ds m).pop 0)).pop 1)).pop 2

theorem reject_run (ds : List Digit) (clear : List Bool) (restore : List Pair) (m : Memory 4)
    (hm0 : m.stack 0=ds.map Digit.bound) (hm1 : m.stack 1=[]) (hm2 : m.stack 2=[])
    (hc : clear.length=ds.length) (hr : restore.map Pair.bit=(ds.map Digit.bound).reverse)
    (ha : ¬beValue (ds.map Digit.coin)≤beValue (ds.map Digit.bound))
    (a b c d : Bool) :
    (rejectBits ds clear restore a b c d).foldl (fun c b => step program b c) (config (.start .eq) m)=
      config (.start .eq) (rejectMemory ds clear restore m) := by
  have hs := pass_stacks ds m hm0
  have h0 : ((wordMemory ds m).pop 0).stack 0=[] := by simp [hs.1]
  have h1 : (((wordMemory ds m).pop 0).stack 1).length=clear.length := by simp [hs.2.1,hm1,hc]
  have hcs := clearWord_stacks clear _ h1
  have h2 : ((clearWord clear ((wordMemory ds m).pop 0)).pop 1).stack 2=restore.map Pair.bit := by
    simp [hcs.2.1 2 (by decide),hs.2.2.1,hm2,hr]
  have hrst := moveWord_stacks restore 2 0 _ (by decide) h2
  unfold rejectBits
  simp only [List.foldl_append]
  rw [pass ds .eq m hm0,decision _ _ hs.1 a b,comparison_correct,ite_eq_right (by simpa using ha)]
  rw [discard_pass clear _ h1]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [discard_finish _ hcs.1 c,restore_pass restore _ h2,restore_finish _ hrst.1 d]
  rfl

theorem reject_stacks (ds : List Digit) (clear : List Bool) (restore : List Pair) (m : Memory 4)
    (hm0 : m.stack 0=ds.map Digit.bound) (hm1 : m.stack 1=[]) (hm2 : m.stack 2=[])
    (hc : clear.length=ds.length) (hr : restore.map Pair.bit=(ds.map Digit.bound).reverse) :
    (rejectMemory ds clear restore m).stack 0=m.stack 0 ∧
    (rejectMemory ds clear restore m).stack 1=[] ∧
    (rejectMemory ds clear restore m).stack 2=[] ∧
    (rejectMemory ds clear restore m).outputRev=m.outputRev := by
  have hs := pass_stacks ds m hm0
  have h0 : ((wordMemory ds m).pop 0).stack 0=[] := by simp [hs.1]
  have h1 : (((wordMemory ds m).pop 0).stack 1).length=clear.length := by simp [hs.2.1,hm1,hc]
  have hcs := clearWord_stacks clear _ h1
  have h2 : ((clearWord clear ((wordMemory ds m).pop 0)).pop 1).stack 2=restore.map Pair.bit := by
    simp [hcs.2.1 2 (by decide),hs.2.2.1,hm2,hr]
  have hrst := moveWord_stacks restore 2 0 _ (by decide) h2
  simp [rejectMemory,hrst.1,hrst.2.1,hrst.2.2 1 (by decide) (by decide),hcs.1,
    hcs.2.1 0 (by decide),hcs.2.2,hs.1,hr,hm0]

theorem reject_length (ds : List Digit) (clear : List Bool) (restore : List Pair)
    (hc : clear.length=ds.length) (hr : restore.map Pair.bit=(ds.map Digit.bound).reverse) (a b c d : Bool) :
    (rejectBits ds clear restore a b c d).length=7*ds.length+4 := by
  have hlr := congrArg List.length hr
  simp only [List.length_map,List.length_reverse] at hlr
  simp only [rejectBits,List.length_append,List.length_cons,List.length_nil,pass_length,pairBits_length,hlr,hc]
  omega

def prepareBits (load restore : List Pair) (a b : Bool) : List Bool :=
  load.flatMap pairBits ++ [a] ++ restore.flatMap pairBits ++ [b]

def prepareMemory (load restore : List Pair) (m : Memory 4) : Memory 4 :=
  (moveWord restore 2 0 (loadWord load m).read).pop 2

theorem prepare_run (load restore : List Pair) (m : Memory 4)
    (hm : m.input=load.map Pair.bit) (hm2 : m.stack 2=[])
    (hr : restore.map Pair.bit=(load.map Pair.bit).reverse) (a b : Bool) :
    (prepareBits load restore a b).foldl (fun c b => step program b c) (config .read m)=
      config (.start .eq) (prepareMemory load restore m) := by
  have hl := loadWord_stacks load m hm
  have h2 : (loadWord load m).read.stack 2=restore.map Pair.bit := by
    simpa [Memory.read,hm2,hr] using hl.2.1
  have hrst := moveWord_stacks restore 2 0 _ (by decide) h2
  unfold prepareBits
  simp only [List.foldl_append]
  rw [load_pass load m hm]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [load_finish _ hl.1 a,restore_pass restore _ h2,restore_finish _ hrst.1 b]
  rfl

theorem prepare_stacks (load restore : List Pair) (m : Memory 4)
    (hm : m.input=load.map Pair.bit) (hm0 : m.stack 0=[]) (hm2 : m.stack 2=[])
    (hr : restore.map Pair.bit=(load.map Pair.bit).reverse) :
    (prepareMemory load restore m).stack 0=m.input ∧
    (prepareMemory load restore m).stack 1=m.stack 1 ∧
    (prepareMemory load restore m).stack 2=[] ∧
    (prepareMemory load restore m).outputRev=m.outputRev := by
  have hl := loadWord_stacks load m hm
  have h2 : (loadWord load m).read.stack 2=restore.map Pair.bit := by
    simpa [Memory.read,hm2,hr] using hl.2.1
  have hrst := moveWord_stacks restore 2 0 _ (by decide) h2
  simp only [prepareMemory,pop_stack,pop_other _ 2 0 (by decide),pop_other _ 2 1 (by decide),pop_output]
  rw [hrst.1,hrst.2.1,hrst.2.2 1 (by decide) (by decide)]
  simp [Memory.read,hl.2.2.1 0 (by decide),hl.2.2.1 1 (by decide),hl.2.2.2,hr,hm0,hm]

theorem prepare_length (load restore : List Pair)
    (hr : restore.map Pair.bit=(load.map Pair.bit).reverse) (a b : Bool) :
    (prepareBits load restore a b).length=4*load.length+2 := by
  have hlr := congrArg List.length hr
  simp only [List.length_map,List.length_reverse] at hlr
  simp only [prepareBits,List.length_append,List.length_cons,List.length_nil,pairBits_length,hlr]
  omega

end
end Contingency.BitModel.StackCode.IntegerDraw

 

 

 

open scoped BigOperators
namespace Contingency.BitModel.StackCode.IntegerDraw
open BinaryTrial
noncomputable section

def digitCoord {n : ℕ} (i : Fin n) (j : Fin 4) : Fin (n*4) := finProdFinEquiv (i,j)

def digitNoise (j : Fin 3) : Fin 4 := if j=0 then 0 else if j=1 then 1 else 3

def blockEquiv (n : ℕ) : (Fin (n*4) → Bool) ≃ (Fin n → Bool)×((Fin n×Fin 3)→Bool) where
  toFun f := (fun i => f (digitCoord i 2),fun ij => f (digitCoord ij.1 (digitNoise ij.2)))
  invFun p k := let ij := finProdFinEquiv.symm k
    if ij.2=2 then p.1 ij.1 else if ij.2=0 then p.2 (ij.1,0)
      else if ij.2=1 then p.2 (ij.1,1) else p.2 (ij.1,2)
  left_inv f := by
    funext k
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective k
    fin_cases j <;> simp [digitCoord,digitNoise]
  right_inv p := by
    rcases p with ⟨f,g⟩
    apply Prod.ext
    · funext i; simp [digitCoord]
    · funext ⟨i,j⟩; fin_cases j <;> simp [digitCoord,digitNoise]

theorem block_count (n : ℕ) (p : (Fin n→Bool)→Prop) [DecidablePred p] :
    (Finset.univ.filter fun c : Fin (n*4)→Bool => p (fun i => c (digitCoord i 2))).card=
      2^(n*3)*(Finset.univ.filter p).card := by
  classical
  simp only [Finset.card_filter]
  change (∑ c,if p ((blockEquiv n c).1) then 1 else 0)=_
  rw [(blockEquiv n).sum_comp (fun ab => if p ab.1 then (1:ℕ) else 0),Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bs _
  by_cases hp : p bs
  · simp [hp]
  · simp [hp]

def digits {n : ℕ} (bound : Fin n → Bool) (coins : Fin (n*4)→Bool) : List Digit :=
  List.ofFn fun i => ⟨bound i,coins (digitCoord i 2),coins (digitCoord i 0),
    coins (digitCoord i 1),coins (digitCoord i 3)⟩

@[simp] theorem digits_length {n : ℕ} (bound : Fin n → Bool) (coins : Fin (n*4)→Bool) :
    (digits bound coins).length=n := by simp [digits]
@[simp] theorem digits_bound {n : ℕ} (bound : Fin n → Bool) (coins : Fin (n*4)→Bool) :
    (digits bound coins).map Digit.bound=List.ofFn bound := by simp [digits,Function.comp_def]
@[simp] theorem digits_coin {n : ℕ} (bound : Fin n → Bool) (coins : Fin (n*4)→Bool) :
    (digits bound coins).map Digit.coin=List.ofFn (fun i => coins (digitCoord i 2)) := by simp [digits,Function.comp_def]

theorem digits_bits {n : ℕ} (bound : Fin n → Bool) (coins : Fin (n*4)→Bool) :
    (digits bound coins).flatMap bits=List.ofFn coins := by
  rw [List.ofFn_mul]
  unfold digits
  rw [List.flatMap_def,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [bits,List.ofFn_succ,digitCoord,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

 
theorem pass_uniform {n : ℕ} (bound : Fin n→Bool) (coins : Fin (n*4)→Bool) (m : Memory 4)
    (hm : m.stack 0=List.ofFn bound) :
    (List.ofFn coins).foldl (fun c b => step program b c) (config (.start .eq) m)=
      config (.start (wordCmp (digits bound coins) .eq)) (wordMemory (digits bound coins) m) := by
  rw [← digits_bits bound coins]
  exact pass _ _ _ (by simpa using hm)

 
theorem candidate_count (n : ℕ) (u : Fin (2^n)) :
    (Finset.univ.filter fun c : Fin (n*4)→Bool => wordFin (fun i => c (digitCoord i 2))=u).card=2^(n*3) := by
  rw [block_count n (fun bs => wordFin bs=u),word_count]
  omega

theorem bounded_words (n M : ℕ) (hM : M<2^n) :
    (Finset.univ.filter fun bs : Fin n→Bool => wordValue bs≤M).card=M+1 := by
  classical
  simp only [Finset.card_filter]
  change (∑ bs,if (wordEquiv n bs).val≤M then 1 else 0)=_
  rw [(wordEquiv n).sum_comp (fun u => if u.val≤M then (1:ℕ) else 0)]
  rw [← Finset.card_filter]
  have he : (Finset.univ.filter fun u : Fin (2^n) => u.val≤M)=Finset.Iic ⟨M,hM⟩ := by ext u; simp [Fin.le_def]
  rw [he]
  simp

theorem accepted_count {n : ℕ} (bound : Fin n→Bool) :
    (Finset.univ.filter fun c : Fin (n*4)→Bool => accept (wordCmp (digits bound c) .eq)=true).card=
      2^(n*3)*(wordValue bound+1) := by
  simp only [comparison_correct,digits_coin,digits_bound,decide_eq_true_eq]
  change (Finset.univ.filter fun c : Fin (n*4)→Bool => wordValue (fun i => c (digitCoord i 2))≤wordValue bound).card=_
  rw [block_count n (fun bs => wordValue bs≤wordValue bound),bounded_words n _ (wordValue_lt bound)]

 
theorem accepted_probability {n : ℕ} (bound : Fin n→Bool) :
    ((Finset.univ.filter fun c : Fin (n*4)→Bool => accept (wordCmp (digits bound c) .eq)=true).card:ℝ)/2^(n*4)=
      (wordValue bound+1:ℝ)/2^n := by
  rw [accepted_count]
  push_cast
  rw [show n*4=n*3+n by omega,pow_add]
  field_simp

end
end Contingency.BitModel.StackCode.IntegerDraw

end

end OAI
