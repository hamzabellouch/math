import Mathlib
import OAI.Analysis.MatrixSigning.Realization.PairRoutine
import OAI.Analysis.MatrixSigning.Realization.FramedMapRoutine

namespace OAI

namespace CurrentKS.FoldRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine PairRoutine

abbrev source (n : ℕ) : Fin (n+5) := ⟨n+1,by omega⟩
abbrev accumulator (n : ℕ) : Fin (n+5) := ⟨n+2,by omega⟩
abbrev work (n : ℕ) : Fin (n+5) := ⟨n+3,by omega⟩
abbrev temp (n : ℕ) : Fin (n+5) := ⟨n+4,by omega⟩
def ports (n : ℕ) : Fin (n+1) ↪ Fin (n+5) := ⟨Fin.castAdd 4,Fin.castAdd_injective _ _⟩
def state (n : ℕ) (value stored tail : Word) : Fin (n+5) → Word :=
  fun j => if j.val=0 then value else if j.val=n+1 then tail else if j.val=n+2 then stored else []

def initialPorts (n : ℕ) : Fin 3 ↪ Fin (n+5) :=
  ⟨![0,accumulator n,work n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩
def decodePorts (n : ℕ) : Fin 3 ↪ Fin (n+5) :=
  ⟨![source n,0,work n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩
def framePorts (n : ℕ) : Fin 3 ↪ Fin (n+5) :=
  ⟨![work n,accumulator n,temp n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩

@[simp] private lemma initialPorts_apply (n : ℕ) (i : Fin 3) :
    initialPorts n i = ![0,accumulator n,work n] i := rfl

@[simp] private lemma decodePorts_apply (n : ℕ) (i : Fin 3) :
    decodePorts n i = ![source n,0,work n] i := rfl

@[simp] private lemma framePorts_apply (n : ℕ) (i : Fin 3) :
    framePorts n i = ![work n,accumulator n,temp n] i := rfl

def setup (n : ℕ) : Program (n+5) :=
  compose (KS.W11.FrameWireCodec.unframeProgram (initialPorts n))
    (CleanRoutine.transfer 0 (work n) (source n))
def decode (n : ℕ) := KS.W11.FrameWireCodec.unframeProgram (decodePorts n)
def frame (n : ℕ) := KS.W11.FrameWireCodec.frameProgram (framePorts n)
def prepend (n : ℕ) := KS.W12.StackTransfer.program (accumulator n) 0 (work n)
def save (n : ℕ) := CleanRoutine.transfer 0 (work n) (accumulator n)
def finish (n : ℕ) := CleanRoutine.transfer (accumulator n) (work n) 0

variable {α β : Type*} {encS : β → Word} {encE : α → Word} {F : β → α → β}
variable {cost : β×α → ℕ}

def body (r : Routine (fun p : β×α => pair (encS p.1) (encE p.2))
    (fun p => encS (F p.1 p.2)) cost) : Program (r.scratch+5) :=
  compose (decode r.scratch) (compose (frame r.scratch) (compose (prepend r.scratch)
    (compose (liftPorts r.program (ports r.scratch)) (save r.scratch))))
def scan (r : Routine (fun p : β×α => pair (encS p.1) (encE p.2))
    (fun p => encS (F p.1 p.2)) cost) :=
  FiniteControl.whileNonempty (source r.scratch) (body r)
def program (r : Routine (fun p : β×α => pair (encS p.1) (encE p.2))
    (fun p => encS (F p.1 p.2)) cost) :=
  compose (setup r.scratch) (compose (scan r) (finish r.scratch))

lemma state_ports (n : ℕ) (a b c : Word) (j : Fin (n+1)) :
    state n a b c (ports n j)=io a j := by
  have h₁ : j.val≠n+1 := by omega
  have h₂ : j.val≠n+2 := by omega
  simp [state,ports,io,h₁,h₂]
lemma state_other (n : ℕ) (a a' b c : Word) (j : Fin (n+5)) (hj : ∀ i,j≠ports n i) :
    state n a b c j=state n a' b c j := by
  have hz : j.val≠0 := by intro hz;exact hj 0 (Fin.ext hz)
  simp [state,hz]

lemma setup_spec (n : ℕ) (a xs : Word) :
    RunSpec (setup n) (io (pair a xs)) (state n [] a xs)
      ((3*a.length+2)+(2*xs.length+2)) := by
  have hd : RunSpec (KS.W11.FrameWireCodec.unframeProgram (initialPorts n))
      (io (pair a xs)) (state n xs a []) (3*a.length+2) := by
    have h := KS.W11.FrameWireCodec.unframe_spec (initialPorts n) (fun _ => []) a xs
    convert h using 1 <;> funext j <;>
      simp only [KS.W28.FixedPositiveSerializer.registers,initialPorts_apply] <;>
      dsimp [state,io] <;>
      simp only [Fin.ext_iff] <;> split_ifs <;> simp_all
  have ht : RunSpec (CleanRoutine.transfer 0 (work n) (source n))
      (state n xs a []) (state n [] a xs) (2*xs.length+2) := by
    have h := CleanRoutine.transfer_spec (0 : Fin (n+5)) (work n) (source n)
      (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (state n xs a []) (by simp [state]) (by simp [state])
    convert h using 1 <;> (try rfl)
    funext j;dsimp [state,Function.update];simp only [Fin.ext_iff];split_ifs <;> simp_all
  exact hd.compose ht

lemma decode_spec (n : ℕ) (s x tail : Word) :
    RunSpec (decode n) (state n [] s (KS.W01.frame x++tail)) (state n x s tail) (3*x.length+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec (decodePorts n) (state n [] s []) x tail
  convert h using 1 <;> (try rfl) <;> funext j <;>
    simp only [KS.W28.FixedPositiveSerializer.registers,decodePorts_apply] <;>
    dsimp [state] <;>
    simp only [Fin.ext_iff] <;> split_ifs <;> simp_all

lemma frame_spec (n : ℕ) (s x tail : Word) :
    RunSpec (frame n) (state n x s tail) (state n x (KS.W01.frame s) tail) (4*s.length+3) := by
  have h := KS.W11.FrameWireCodec.frame_spec (framePorts n) (state n x [] tail) s
  convert h using 1 <;> (try rfl) <;> funext j <;>
    simp only [KS.W28.FixedPositiveSerializer.registers,framePorts_apply] <;>
    dsimp [state] <;>
    simp only [Fin.ext_iff] <;> split_ifs <;> simp_all

lemma prepend_spec (n : ℕ) (s x tail : Word) :
    RunSpec (prepend n) (state n x s tail) (state n (s++x) [] tail) (2*s.length+2) := by
  have h := KS.W12.StackTransfer.spec (accumulator n) (0 : Fin (n+5)) (work n)
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (state n x s tail) (by simp [state])
  convert h using 1 <;> (try rfl)
  · funext j;dsimp [state,KS.W12.StackTransfer.after];simp only [Fin.ext_iff];split_ifs <;> simp_all
  · simp [state]

lemma save_spec (n : ℕ) (s tail : Word) :
    RunSpec (save n) (state n s [] tail) (state n [] s tail) (2*s.length+2) := by
  have h := CleanRoutine.transfer_spec (0 : Fin (n+5)) (work n) (accumulator n)
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (state n s [] tail) (by simp [state]) (by simp [state])
  convert h using 1 <;> (try rfl)
  funext j;dsimp [state,Function.update];simp only [Fin.ext_iff];split_ifs <;> simp_all

lemma finish_spec (n : ℕ) (s : Word) :
    RunSpec (finish n) (state n [] s []) (io s) (2*s.length+2) := by
  have h := CleanRoutine.transfer_spec (accumulator n) (work n) (0 : Fin (n+5))
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (state n [] s []) (by simp [state]) (by simp [state])
  convert h using 1 <;> (try rfl)
  · funext j;dsimp [state,io,Function.update];simp only [Fin.ext_iff];split_ifs <;> simp_all
  · simp [state]

def bodyTicks (encS : β → Word) (encE : α → Word) (F : β → α → β) (cost : β×α → ℕ)
    (s : β) (x : α) : ℕ :=
  (3*(encE x).length+2)+(4*(encS s).length+3)+(2*(KS.W01.frame (encS s)).length+2)+
    cost (s,x)+(2*(encS (F s x)).length+2)

lemma body_spec (r : Routine (fun p : β×α => pair (encS p.1) (encE p.2))
    (fun p => encS (F p.1 p.2)) cost) (s : β) (x : α) (tail : Word) :
    RunSpec (body r) (state r.scratch [] (encS s) (KS.W01.frame (encE x)++tail))
      (state r.scratch [] (encS (F s x)) tail) (bodyTicks encS encE F cost s x) := by
  have hc := KS.W01.FixedPortRunSpec.lift_runSpec _ (ports r.scratch) _ _
    (state r.scratch (pair (encS s) (encE x)) [] tail)
    (state r.scratch (encS (F s x)) [] tail) _ (r.spec (s,x))
    (state_ports _ _ _ _) (state_ports _ _ _ _) (state_other _ _ _ _ _)
  have h := (decode_spec r.scratch (encS s) (encE x) tail).compose
    ((frame_spec r.scratch (encS s) (encE x) tail).compose
      ((prepend_spec r.scratch (KS.W01.frame (encS s)) (encE x) tail).compose
        (hc.compose (save_spec r.scratch (encS (F s x)) tail))))
  simp only [bodyTicks,Nat.add_assoc] at h ⊢
  exact h

def scanTicks (encS : β → Word) (encE : α → Word) (F : β → α → β) (cost : β×α → ℕ) : β → List α → ℕ
  | _,[] => 1
  | s,x::xs => bodyTicks encS encE F cost s x+scanTicks encS encE F cost (F s x) xs+1

lemma scan_trace (r : Routine (fun p : β×α => pair (encS p.1) (encE p.2))
    (fun p => encS (F p.1 p.2)) cost) (s : β) (xs : List α) :
    FiniteControl.Trace (source r.scratch) (body r)
      (state r.scratch [] (encS s) (FramedMapRoutine.tape encE xs))
      (state r.scratch [] (encS (xs.foldl F s)) []) (scanTicks encS encE F cost s xs) := by
  induction xs generalizing s with
  | nil =>
    exact FiniteControl.Trace.stop _ (by simp [state,FramedMapRoutine.tape])
  | cons x xs ih =>
    apply FiniteControl.Trace.step ?_ (body_spec r s x (FramedMapRoutine.tape encE xs)) (ih (F s x))
    intro hz
    have hh := congrArg List.length hz
    simp [state,KS.W01.length_frame] at hh

def ticks (encS : β → Word) (encE : α → Word) (F : β → α → β) (cost : β×α → ℕ)
    (s : β) (xs : List α) : ℕ :=
  ((3*(encS s).length+2)+(2*(FramedMapRoutine.tape encE xs).length+2))+
    scanTicks encS encE F cost s xs+(2*(encS (xs.foldl F s)).length+2)

def routine (r : Routine (fun p : β×α => pair (encS p.1) (encE p.2))
    (fun p => encS (F p.1 p.2)) cost) :
    Routine (fun p : β×List α => pair (encS p.1) (FramedMapRoutine.tape encE p.2))
      (fun p => encS (p.2.foldl F p.1)) (fun p => ticks encS encE F cost p.1 p.2) where
  scratch := r.scratch+4
  program := program r
  spec p := by
    have h := (setup_spec r.scratch (encS p.1) (FramedMapRoutine.tape encE p.2)).compose
      ((FiniteControl.trace_spec (scan_trace r p.1 p.2)).compose
        (finish_spec r.scratch (encS (p.2.foldl F p.1))))
    simp only [ticks,Nat.add_assoc] at h ⊢
    exact h

end CurrentKS.FoldRoutine

end OAI
