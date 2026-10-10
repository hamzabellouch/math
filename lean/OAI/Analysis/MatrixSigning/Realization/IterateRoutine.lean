import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FiniteControl
import OAI.Analysis.MatrixSigning.Realization.CleanRoutine
import OAI.Analysis.MatrixSigning.Machines.LiteralProgram

namespace OAI

namespace CurrentKS.IterateRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine

variable {α : Type*} {encode : α → Word} {next : α → α} {cost : α → ℕ}

abbrev counter (n : ℕ) : Fin (n+3) := ⟨n+1,by omega⟩
abbrev work (n : ℕ) : Fin (n+3) := ⟨n+2,by omega⟩
def corePorts (n : ℕ) : Fin (n+1) ↪ Fin (n+3) := ⟨Fin.castAdd 2,Fin.castAdd_injective _ _⟩
def parsePorts (n : ℕ) : Fin 3 ↪ Fin (n+3) :=
  ⟨![0,counter n,work n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩
@[simp] private lemma parsePorts_apply (n : ℕ) (i : Fin 3) :
    parsePorts n i = ![0,counter n,work n] i := rfl

def state (n : ℕ) (value count : Word) : Fin (n+3) → Word :=
  fun j => if j.val=0 then value else if j.val=n+1 then count else []
def parse (n : ℕ) : Program (n+3) := KS.W11.FrameWireCodec.unframeProgram (parsePorts n)
def body (r : Routine encode (fun x => encode (next x)) cost) : Program (r.scratch+3) :=
  compose (KS.W23.LiteralProgram.pop (counter r.scratch)) (liftPorts r.program (corePorts r.scratch))
def program (r : Routine encode (fun x => encode (next x)) cost) : Program (r.scratch+3) :=
  compose (parse r.scratch) (FiniteControl.whileNonempty (counter r.scratch) (body r))
def input (encode : α → Word) (p : ℕ×α) : Word :=
  KS.W01.frame (List.replicate p.1 true)++encode p.2

lemma parse_spec (n : ℕ) (value : Word) (k : ℕ) :
    RunSpec (parse n) (io (KS.W01.frame (List.replicate k true)++value))
      (state n value (List.replicate k true)) (3*k+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec (parsePorts n) (fun _ => []) (List.replicate k true) value
  convert h using 1 <;> (try rfl)
  · funext j
    simp only [KS.W28.FixedPositiveSerializer.registers,parsePorts_apply]
    dsimp [io]
    simp only [Fin.ext_iff,Fin.val_zero]
    split_ifs <;> simp_all
  · funext j
    simp only [KS.W28.FixedPositiveSerializer.registers,parsePorts_apply]
    dsimp [state]
    simp only [Fin.ext_iff,Fin.val_zero]
    split_ifs <;> simp_all
  · simp

lemma element_spec (r : Routine encode (fun x => encode (next x)) cost) (x : α) (count : Word) :
    RunSpec (liftPorts r.program (corePorts r.scratch))
      (state r.scratch (encode x) count) (state r.scratch (encode (next x)) count) (cost x) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (r.spec x)
  · intro j
    have hj : j.val≠r.scratch+1 := by omega
    simp [state,io,corePorts,hj]
  · intro j
    have hj : j.val≠r.scratch+1 := by omega
    simp [state,io,corePorts,hj]
  · intro j hj
    have hz : j.val≠0 := by intro hz;exact hj 0 (Fin.ext hz)
    simp [state,hz]

lemma pop_spec (n : ℕ) (value : Word) (k : ℕ) :
    RunSpec (KS.W23.LiteralProgram.pop (counter n)) (state n value (List.replicate (k+1) true))
      (state n value (List.replicate k true)) 1 := by
  have h := KS.W23.LiteralProgram.pop_spec (counter n) (state n value (List.replicate (k+1) true))
  convert h using 1
  funext j
  dsimp [state,Function.update]
  simp only [Fin.ext_iff]
  split_ifs <;> simp_all

def loopTicks (cost : α → ℕ) (next : α → α) : ℕ → α → ℕ
  | 0,_ => 1
  | k+1,x => (1+cost x)+loopTicks cost next k (next x)+1

lemma loop_trace (r : Routine encode (fun x => encode (next x)) cost) (k : ℕ) (x : α) :
    FiniteControl.Trace (counter r.scratch) (body r)
      (state r.scratch (encode x) (List.replicate k true))
      (io (encode (next^[k] x))) (loopTicks cost next k x) := by
  induction k generalizing x with
  | zero =>
    have he : state r.scratch (encode x) []=io (encode x) := by funext j;simp [state,io]
    simpa only [List.replicate_zero,Function.iterate_zero_apply,loopTicks,he] using
      (FiniteControl.Trace.stop (body:=body r) (port:=counter r.scratch)
        (state r.scratch (encode x) []) (by simp [state]))
  | succ k ih =>
    have hb := (pop_spec r.scratch (encode x) k).compose (element_spec r x (List.replicate k true))
    have h := FiniteControl.Trace.step (show state r.scratch (encode x)
        (List.replicate (k+1) true) (counter r.scratch)≠[] by simp [state]) hb (ih (next x))
    simp only [Function.iterate_succ_apply,loopTicks] at h ⊢
    exact h

def routine (r : Routine encode (fun x => encode (next x)) cost) :
    Routine (input encode) (fun p : ℕ×α => encode (next^[p.1] p.2))
      (fun p => 3*p.1+2+loopTicks cost next p.1 p.2) where
  scratch := r.scratch+2
  program := program r
  spec p := (parse_spec r.scratch (encode p.2) p.1).compose
    (FiniteControl.trace_spec (loop_trace r p.1 p.2))

lemma loopTicks_le (k : ℕ) (x : α) (B : ℕ)
    (h : ∀ j<k,cost (next^[j] x)≤B) : loopTicks cost next k x≤k*(B+2)+1 := by
  induction k generalizing x with
  | zero => simp [loopTicks]
  | succ k ih =>
    have hx : cost x≤B := by simpa using h 0 (by omega)
    have hi := ih (next x) (by
      intro j hj
      simpa only [Function.iterate_succ_apply] using h (j+1) (by omega))
    simp only [loopTicks]
    nlinarith

end CurrentKS.IterateRoutine

end OAI
