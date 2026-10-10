import Mathlib
import OAI.Analysis.MatrixSigning.Model
import OAI.Analysis.MatrixSigning.Machines.FiniteControl
import OAI.Analysis.MatrixSigning.Realization.CleanRoutine

namespace OAI

namespace CurrentKS.FramedMapRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine

variable {α : Type*} {input output : α → Word} {cost : α → ℕ}

abbrev source (n : ℕ) : Fin (n+5) := ⟨n+1,by omega⟩
abbrev accumulator (n : ℕ) : Fin (n+5) := ⟨n+2,by omega⟩
abbrev work (n : ℕ) : Fin (n+5) := ⟨n+3,by omega⟩
abbrev scratch (n : ℕ) : Fin (n+5) := ⟨n+4,by omega⟩

def state (n : ℕ) (value tail acc : Word) : Fin (n+5) → Word :=
  fun j => if j.val=0 then value else if j.val=n+1 then tail else if j.val=n+2 then acc else []

def ports (n : ℕ) : Fin (n+1) ↪ Fin (n+5) := ⟨Fin.castAdd 4,Fin.castAdd_injective _ _⟩
def decodePorts (n : ℕ) : Fin 3 ↪ Fin (n+5) :=
  ⟨![source n,0,work n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩
def framePorts (n : ℕ) : Fin 3 ↪ Fin (n+5) :=
  ⟨![work n,0,scratch n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩

private lemma decodePorts_0 (n : ℕ) : decodePorts n 0 = source n := rfl
private lemma decodePorts_1 (n : ℕ) : decodePorts n 1 = 0 := rfl
private lemma decodePorts_2 (n : ℕ) : decodePorts n 2 = work n := rfl
private lemma framePorts_0 (n : ℕ) : framePorts n 0 = work n := rfl
private lemma framePorts_1 (n : ℕ) : framePorts n 1 = 0 := rfl
private lemma framePorts_2 (n : ℕ) : framePorts n 2 = scratch n := rfl

def decode (n : ℕ) : Program (n+5) := KS.W11.FrameWireCodec.unframeProgram (decodePorts n)
def frame (n : ℕ) : Program (n+5) := KS.W11.FrameWireCodec.frameProgram (framePorts n)
def append (n : ℕ) : Program (n+5) := KS.W04.BinaryStackMoves.moveProgram 0 (accumulator n)
def body (r : Routine input output cost) : Program (r.scratch+5) :=
  compose (decode r.scratch) (compose (liftPorts r.program (ports r.scratch))
    (compose (frame r.scratch) (append r.scratch)))
def scan (r : Routine input output cost) : Program (r.scratch+5) :=
  FiniteControl.whileNonempty (source r.scratch) (body r)
def setup (n : ℕ) : Program (n+5) := CleanRoutine.transfer 0 (work n) (source n)
def finish (n : ℕ) : Program (n+5) := KS.W04.BinaryStackMoves.moveProgram (accumulator n) 0

def program (r : Routine input output cost) : Program (r.scratch+5) :=
  compose (setup r.scratch) (compose (scan r) (finish r.scratch))

def tape (encode : α → Word) (xs : List α) := xs.flatMap (fun x => KS.W01.frame (encode x))

lemma state_ports (n : ℕ) (value tail acc : Word) (i : Fin (n+1)) :
    state n value tail acc (ports n i)=io value i := by
  have h₁ : i.val≠n+1 := by omega
  have h₂ : i.val≠n+2 := by omega
  simp [state,ports,io,h₁,h₂]

lemma state_other (n : ℕ) (u v tail acc : Word) (j : Fin (n+5))
    (hj : ∀ i,j≠ports n i) : state n u tail acc j=state n v tail acc j := by
  have hz : j.val≠0 := by intro hz;exact hj 0 (Fin.ext hz)
  simp [state,hz]

lemma element_spec (r : Routine input output cost) (x : α) (tail acc : Word) :
    RunSpec (liftPorts r.program (ports r.scratch))
      (state r.scratch (input x) tail acc) (state r.scratch (output x) tail acc) (cost x) := by
  exact KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (r.spec x)
    (state_ports _ _ _ _) (state_ports _ _ _ _) (state_other _ _ _ _ _)

lemma decode_spec (n : ℕ) (value tail acc : Word) :
    RunSpec (decode n) (state n [] (KS.W01.frame value++tail) acc)
      (state n value tail acc) (3*value.length+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec (decodePorts n) (state n [] [] acc) value tail
  convert h using 1 <;> (try rfl) <;> funext j <;>
    simp only [KS.W28.FixedPositiveSerializer.registers,decodePorts_0,decodePorts_1,decodePorts_2,
      state,source,work,Fin.ext_iff,Fin.val_zero] <;>
    split_ifs <;> simp_all

lemma frame_spec (n : ℕ) (value tail acc : Word) :
    RunSpec (frame n) (state n value tail acc) (state n (KS.W01.frame value) tail acc)
      (4*value.length+3) := by
  have h := KS.W11.FrameWireCodec.frame_spec (framePorts n) (state n [] tail acc) value
  convert h using 1 <;> (try rfl) <;> funext j <;>
    simp only [KS.W28.FixedPositiveSerializer.registers,framePorts_0,framePorts_1,framePorts_2,
      state,work,scratch,Fin.ext_iff,Fin.val_zero] <;>
    split_ifs <;> simp_all

lemma append_spec (n : ℕ) (value tail acc : Word) :
    RunSpec (append n) (state n value tail acc) (state n [] tail (value.reverse++acc))
      (value.length+1) := by
  have h := KS.W15.RationalMultiply.move_spec (0 : Fin (n+5)) (accumulator n)
    (by simp [Fin.ext_iff]) (state n value tail acc)
  convert h using 1 <;> (try rfl)
  · funext j
    dsimp [state,KS.W15.RationalMultiply.moveAfter]
    simp only [Fin.ext_iff,Fin.val_zero]
    split_ifs <;> simp_all

def bodyTicks (input output : α → Word) (cost : α → ℕ) (x : α) :=
  (3*(input x).length+2)+cost x+(4*(output x).length+3)+
    ((KS.W01.frame (output x)).length+1)

lemma body_spec (r : Routine input output cost) (x : α) (tail acc : Word) :
    RunSpec (body r) (state r.scratch [] (KS.W01.frame (input x)++tail) acc)
      (state r.scratch [] tail ((KS.W01.frame (output x)).reverse++acc))
      (bodyTicks input output cost x) := by
  have h := (decode_spec r.scratch (input x) tail acc).compose
    ((element_spec r x tail acc).compose ((frame_spec r.scratch (output x) tail acc).compose
      (append_spec r.scratch (KS.W01.frame (output x)) tail acc)))
  simp only [bodyTicks,Nat.add_assoc] at h ⊢
  exact h

def scanTicks (input output : α → Word) (cost : α → ℕ) (xs : List α) : ℕ :=
  (xs.map (fun x => bodyTicks input output cost x+1)).sum+1

lemma scan_trace (r : Routine input output cost) (xs : List α) (acc : Word) :
    FiniteControl.Trace (source r.scratch) (body r)
      (state r.scratch [] (tape input xs) acc)
      (state r.scratch [] [] ((tape output xs).reverse++acc)) (scanTicks input output cost xs) := by
  induction xs generalizing acc with
  | nil =>
    simpa [tape,scanTicks] using (FiniteControl.Trace.stop (body := body r)
      (port := source r.scratch) (state r.scratch [] [] acc) (by simp [state]))
  | cons x xs ih =>
    have hs : state r.scratch [] (KS.W01.frame (input x)++tape input xs) acc (source r.scratch)≠[] := by
      have hn : KS.W01.frame (input x) ≠ [] := by
        intro he
        have hl := KS.W01.length_frame (input x)
        rw [he] at hl
        simp only [List.length_nil] at hl
        omega
      simpa [state] using (List.append_ne_nil_of_left_ne_nil hn _ : KS.W01.frame (input x)++tape input xs≠[])
    have h := FiniteControl.Trace.step hs (body_spec r x (tape input xs) acc)
      (ih ((KS.W01.frame (output x)).reverse++acc))
    have hc : bodyTicks input output cost x+scanTicks input output cost xs+1 =
        scanTicks input output cost (x::xs) := by simp [scanTicks]; omega
    rw [hc] at h
    simpa only [tape,List.flatMap_cons,List.reverse_append,List.append_assoc] using h

lemma setup_spec (n : ℕ) (word : Word) :
    RunSpec (setup n) (io word) (state n [] word []) (2*word.length+2) := by
  have h := CleanRoutine.transfer_spec (0 : Fin (n+5)) (work n) (source n)
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (io word) (by simp [io]) (by simp [io])
  convert h using 1 <;> (try rfl)
  funext j
  dsimp [state,io,Function.update]
  simp only [Fin.ext_iff,Fin.val_zero]
  split_ifs <;> simp_all

lemma finish_spec (n : ℕ) (word : Word) :
    RunSpec (finish n) (state n [] [] word.reverse) (io word) (word.length+1) := by
  have h := KS.W15.RationalMultiply.move_spec (accumulator n) (0 : Fin (n+5))
    (by simp [Fin.ext_iff]) (state n [] [] word.reverse)
  convert h using 1 <;> (try rfl)
  · funext j
    dsimp [state,io,KS.W15.RationalMultiply.moveAfter]
    simp only [Fin.ext_iff,Fin.val_zero]
    split_ifs <;> simp_all
  · simp [state]

def ticks (input output : α → Word) (cost : α → ℕ) (xs : List α) :=
  2*(tape input xs).length+2+scanTicks input output cost xs+(tape output xs).length+1

def routine (r : Routine input output cost) :
    Routine (tape input) (tape output) (ticks input output cost) where
  scratch := r.scratch+4
  program := program r
  spec xs := by
    have h := FiniteControl.trace_spec (scan_trace r xs [])
    simp only [List.append_nil] at h
    have h' := (setup_spec r.scratch (tape input xs)).compose
      (h.compose (finish_spec r.scratch (tape output xs)))
    simp only [ticks,Nat.add_assoc] at h' ⊢
    exact h'

end CurrentKS.FramedMapRoutine

end OAI
