import Mathlib
import OAI.Analysis.MatrixSigning.Realization.CleanRoutine
import OAI.Analysis.MatrixSigning.Machines.InputHeaderPrimitives
import OAI.Analysis.MatrixSigning.Machines.StackTransfer

namespace OAI

namespace CurrentKS.PairRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine

abbrev pair (a b : Word) : Word := KS.W01.frame a++b

def smallState (value saved work : Word) : Fin 3 → Word := ![value,saved,work]
def split : Program 3 := KS.W11.FrameWireCodec.unframeProgram ⟨![0,1,2],by decide⟩
def first : Program 3 := compose split (compose (KS.W04.BinaryStackMoves.clearProgram 0)
  (CleanRoutine.transfer 1 2 0))
def second : Program 3 := compose split (KS.W04.BinaryStackMoves.clearProgram 1)

lemma split_spec (a b : Word) : RunSpec split (io (pair a b)) (smallState b a []) (3*a.length+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec (⟨![0,1,2],by decide⟩ : Fin 3 ↪ Fin 3)
    (fun _ => []) a b
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [io,smallState,KS.W28.FixedPositiveSerializer.registers])

lemma clear_first (a b : Word) :
    RunSpec (KS.W04.BinaryStackMoves.clearProgram (0 : Fin 3)) (smallState b a [])
      (smallState [] a []) (b.length+1) := by
  have h := KS.W15.RationalMultiply.clear_spec (0 : Fin 3) (smallState b a [])
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [smallState,KS.W15.RationalMultiply.clearAfter]

lemma take_first (a : Word) :
    RunSpec (CleanRoutine.transfer (1 : Fin 3) 2 0) (smallState [] a []) (io a) (2*a.length+2) := by
  have h := CleanRoutine.transfer_spec (1 : Fin 3) 2 0 (by decide) (by decide) (by decide)
    (smallState [] a []) rfl rfl
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [smallState,io,Function.update]

lemma clear_second (a b : Word) :
    RunSpec (KS.W04.BinaryStackMoves.clearProgram (1 : Fin 3)) (smallState b a [])
      (io b) (a.length+1) := by
  have h := KS.W15.RationalMultiply.clear_spec (1 : Fin 3) (smallState b a [])
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [smallState,io,KS.W15.RationalMultiply.clearAfter]

def fstRoutine : Routine (fun p : Word×Word => pair p.1 p.2) Prod.fst
    (fun p => 5*p.1.length+p.2.length+5) where
  scratch := 2
  program := first
  spec p := by
    have h := (split_spec p.1 p.2).compose ((clear_first p.1 p.2).compose (take_first p.1))
    convert h using 1 <;> first | rfl | omega

def sndRoutine : Routine (fun p : Word×Word => pair p.1 p.2) Prod.snd
    (fun p => 4*p.1.length+3) where
  scratch := 2
  program := second
  spec p := by
    have h := (split_spec p.1 p.2).compose (clear_second p.1 p.2)
    convert h using 1 <;> first | rfl | omega

abbrev saved (n : ℕ) : Fin (n+4) := ⟨n+1,by omega⟩
abbrev left (n : ℕ) : Fin (n+4) := ⟨n+2,by omega⟩
abbrev work (n : ℕ) : Fin (n+4) := ⟨n+3,by omega⟩
def ports (n : ℕ) : Fin (n+1) ↪ Fin (n+4) := ⟨Fin.castAdd 3,Fin.castAdd_injective _ _⟩
def state (n : ℕ) (value original first : Word) : Fin (n+4) → Word :=
  fun j => if j.val=0 then value else if j.val=n+1 then original else if j.val=n+2 then first else []
def copyPorts (n : ℕ) : Fin 3 ↪ Fin (n+4) :=
  ⟨![0,saved n,work n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩
def framePorts (n : ℕ) : Fin 3 ↪ Fin (n+4) :=
  ⟨![work n,0,left n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩

@[simp] private lemma copyPorts_apply (n : ℕ) (i : Fin 3) :
    copyPorts n i = ![0,saved n,work n] i := rfl

@[simp] private lemma framePorts_apply (n : ℕ) (i : Fin 3) :
    framePorts n i = ![work n,0,left n] i := rfl

lemma projection (n : ℕ) (a b c : Word) (j : Fin (n+1)) :
    state n a b c (ports n j)=io a j := by
  have h₁ : j.val≠n+1 := by omega
  have h₂ : j.val≠n+2 := by omega
  simp [state,ports,io,h₁,h₂]

lemma outside (n : ℕ) (a a' b c : Word) (j : Fin (n+4)) (hj : ∀ i,j≠ports n i) :
    state n a b c j=state n a' b c j := by
  have hz : j.val≠0 := by intro hz;exact hj 0 (Fin.ext hz)
  simp [state,hz]

variable {α : Type*} {input output : α → Word} {cost : α → ℕ}

lemma element_spec (r : Routine input output cost) (x : α) (original first : Word) :
    RunSpec (liftPorts r.program (ports r.scratch))
      (state r.scratch (input x) original first) (state r.scratch (output x) original first) (cost x) :=
  KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (r.spec x)
    (projection _ _ _ _) (projection _ _ _ _) (outside _ _ _ _ _)

lemma copy_spec (n : ℕ) (w : Word) :
    RunSpec (KS.W01.FixedCopy.program (copyPorts n)) (io w) (state n w w []) (2*w.length+2) := by
  have h := KS.W03.InputHeaderPrimitives.copy_spec (copyPorts n) (io w) w rfl (by simp [io]) (by simp [io])
  convert h using 1
  funext j
  simp only [copyPorts_apply]
  dsimp [state,io,Function.update]
  simp only [Fin.ext_iff]
  split_ifs <;> simp_all

lemma frame_spec (n : ℕ) (a original : Word) :
    RunSpec (KS.W11.FrameWireCodec.frameProgram (framePorts n)) (state n a original [])
      (state n (KS.W01.frame a) original []) (4*a.length+3) := by
  have h := KS.W11.FrameWireCodec.frame_spec (framePorts n) (state n [] original []) a
  convert h using 1 <;> first | rfl |
    (funext j; simp only [KS.W28.FixedPositiveSerializer.registers,framePorts_apply]
     dsimp [state]
     simp only [Fin.ext_iff,Fin.val_zero]
     split_ifs <;> simp_all)

lemma save_first_spec (n : ℕ) (a original : Word) :
    RunSpec (CleanRoutine.transfer 0 (work n) (left n)) (state n a original [])
      (state n [] original a) (2*a.length+2) := by
  have h := CleanRoutine.transfer_spec (0 : Fin (n+4)) (work n) (left n)
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (state n a original []) (by simp [state]) (by simp [state])
  convert h using 1 <;> (try rfl)
  funext j
  dsimp [state,Function.update]
  simp only [Fin.ext_iff,Fin.val_zero]
  split_ifs <;> simp_all

lemma restore_spec (n : ℕ) (original first : Word) :
    RunSpec (CleanRoutine.transfer (saved n) (work n) 0) (state n [] original first)
      (state n original [] first) (2*original.length+2) := by
  have h := CleanRoutine.transfer_spec (saved n) (work n) (0 : Fin (n+4))
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (state n [] original first) (by simp [state]) (by simp [state])
  convert h using 1
  · funext j
    dsimp [state,Function.update]
    simp only [Fin.ext_iff,Fin.val_zero]
    split_ifs <;> simp_all
  · simp [state]

lemma prepend_spec (n : ℕ) (a b : Word) :
    RunSpec (KS.W12.StackTransfer.program (left n) 0 (work n)) (state n b [] a)
      (io (a++b)) (2*a.length+2) := by
  have h := KS.W12.StackTransfer.spec (left n) (0 : Fin (n+4)) (work n)
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (state n b [] a) (by simp [state])
  convert h using 1
  · funext j
    dsimp [state,io,KS.W12.StackTransfer.after]
    simp only [Fin.ext_iff,Fin.val_zero]
    split_ifs <;> simp_all
  · simp [state]

variable {outR outS : α → Word} {cR cS : α → ℕ}

def pairingProgram (n : ℕ) (P Q : Program (n+1)) : Program (n+4) :=
  compose (KS.W01.FixedCopy.program (copyPorts n))
    (compose (liftPorts P (ports n))
      (compose (KS.W11.FrameWireCodec.frameProgram (framePorts n))
        (compose (CleanRoutine.transfer 0 (work n) (left n))
          (compose (CleanRoutine.transfer (saved n) (work n) 0)
            (compose (liftPorts Q (ports n))
              (KS.W12.StackTransfer.program (left n) 0 (work n)))))))

def pairingTicks (input outR : α → Word) (cR cS : α → ℕ) (x : α) :=
  (2*(input x).length+2)+cR x+(4*(outR x).length+3)+
    (2*(KS.W01.frame (outR x)).length+2)+(2*(input x).length+2)+cS x+
    (2*(KS.W01.frame (outR x)).length+2)

lemma pairing_spec (n : ℕ) (P Q : Program (n+1)) (w a b : Word) (c d : ℕ)
    (hP : RunSpec P (io w) (io a) c) (hQ : RunSpec Q (io w) (io b) d) :
    RunSpec (pairingProgram n P Q) (io w) (io (pair a b))
      ((2*w.length+2)+c+(4*a.length+3)+(2*(KS.W01.frame a).length+2)+
        (2*w.length+2)+d+(2*(KS.W01.frame a).length+2)) := by
  have hp := KS.W01.FixedPortRunSpec.lift_runSpec P (ports n) _ _
    (state n w w []) (state n a w []) _ hP
    (projection _ _ _ _) (projection _ _ _ _) (outside _ _ _ _ _)
  have hq := KS.W01.FixedPortRunSpec.lift_runSpec Q (ports n) _ _
    (state n w [] (KS.W01.frame a)) (state n b [] (KS.W01.frame a)) _ hQ
    (projection _ _ _ _) (projection _ _ _ _) (outside _ _ _ _ _)
  have h := (copy_spec n w).compose (hp.compose ((frame_spec n a w).compose
    ((save_first_spec n (KS.W01.frame a) w).compose
      ((restore_spec n w (KS.W01.frame a)).compose (hq.compose (prepend_spec n (KS.W01.frame a) b))))))
  simp only [Nat.add_assoc] at h ⊢
  exact h

def pairing (r : Routine input outR cR) (s : Routine input outS cS) :
    Routine input (fun x => pair (outR x) (outS x)) (pairingTicks input outR cR cS) :=
  let n := r.scratch+s.scratch
  let r' := r.pad n (Nat.le_add_right _ _)
  let s' := s.pad n (Nat.le_add_left _ _)
  { scratch := n+3
    program := pairingProgram n r'.program s'.program
    spec := fun x => pairing_spec n r'.program s'.program _ _ _ _ _ (r'.spec x) (s'.spec x) }

end CurrentKS.PairRoutine

end OAI
