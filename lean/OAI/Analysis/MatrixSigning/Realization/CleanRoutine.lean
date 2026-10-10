import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedPortRunSpec
import OAI.Analysis.MatrixSigning.Machines.StackTransferSpecs
import OAI.Analysis.MatrixSigning.Encoding.FrameWireCodec

namespace OAI

section

namespace CurrentKS.CleanRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

abbrev Word := List Bool

def io {n : ℕ} (w : Word) : Fin (n+1) → Word := fun j => if j.val=0 then w else []

@[simp] lemma io_zero {n : ℕ} (w : Word) : @io n w 0=w := by simp [io]
@[simp] lemma io_ne {n : ℕ} (w : Word) (j : Fin (n+1)) (hj : j.val≠0) : io w j=[] := by simp [io,hj]

structure Routine {α : Type*} (input output : α → Word) (cost : α → ℕ) where
  scratch : ℕ
  program : Program (scratch+1)
  spec : ∀ x,RunSpec program (io (input x)) (io (output x)) (cost x)

def embedding {n m : ℕ} (h : n≤ m) : Fin (n+1) ↪ Fin (m+1) :=
  ⟨Fin.castLE (Nat.add_le_add_right h 1),Fin.castLE_injective _⟩

@[simp] lemma io_embedding {n m : ℕ} (h : n≤ m) (w : Word) (j : Fin (n+1)) :
    io w (embedding h j)=io w j := rfl

lemma io_other {n m : ℕ} (h : n≤ m) (u v : Word) (j : Fin (m+1))
    (hj : ∀ i,j≠embedding h i) : io u j=io v j := by
  have hz : j.val≠0 := by
    intro hz
    exact hj 0 (Fin.ext hz)
  simp [io,hz]

def Routine.pad {α : Type*} {input output : α → Word} {cost : α → ℕ}
    (r : Routine input output cost) (m : ℕ) (hm : r.scratch≤ m) : Routine input output cost where
  scratch := m
  program := liftPorts r.program (embedding hm)
  spec x := KS.W01.FixedPortRunSpec.lift_runSpec r.program (embedding hm)
    _ _ _ _ _ (r.spec x) (io_embedding hm _) (io_embedding hm _) (io_other hm _ _)

def Routine.compose {α : Type*} {first middle last : α → Word} {c d : α → ℕ}
    (r : Routine first middle c) (s : Routine middle last d) :
    Routine first last (fun x => c x+d x) :=
  let r' := r.pad (r.scratch+s.scratch) (Nat.le_add_right _ _)
  let s' := s.pad (r.scratch+s.scratch) (Nat.le_add_left _ _)
  { scratch := r.scratch+s.scratch
    program := KS.W29.FixedSequential.compose r'.program s'.program
    spec := fun x => (r'.spec x).compose (s'.spec x) }

def Routine.reindex {α β : Type*} {input output : α → Word} {cost : α → ℕ}
    (r : Routine input output cost) (f : β → α) :
    Routine (fun x => input (f x)) (fun x => output (f x)) (fun x => cost (f x)) where
  scratch := r.scratch
  program := r.program
  spec x := r.spec (f x)

def Routine.weaken {α : Type*} {input output : α → Word} {c d : α → ℕ}
    (r : Routine input output c) (h : ∀ x,c x≤d x) : Routine input output d where
  scratch := r.scratch
  program := r.program
  spec x := (r.spec x).mono (h x)

def framing : Routine (fun w : Word => w) KS.W01.frame (fun w => 4*w.length+3) where
  scratch := 2
  program := KS.W11.FrameWireCodec.frameProgram ⟨![1,0,2],by decide⟩
  spec w := by
    have h := KS.W11.FrameWireCodec.frame_spec (⟨![1,0,2],by decide⟩ : Fin 3 ↪ Fin 3)
      (fun _ => []) w
    convert h using 1 <;> funext j <;> fin_cases j <;>
      simp [io,KS.W28.FixedPositiveSerializer.registers]

def transfer {k : ℕ} (source work target : Fin k) : Program k :=
  compose (KS.W04.BinaryStackMoves.moveProgram source work)
    (KS.W04.BinaryStackMoves.moveProgram work target)

lemma transfer_spec {k : ℕ} (source work target : Fin k)
    (hsw : source≠work) (hst : source≠target) (hwt : work≠target)
    (s : Fin k → Word) (hw : s work=[]) (ht : s target=[]) :
    RunSpec (transfer source work target) s
      (Function.update (Function.update s source []) target (s source)) (2*(s source).length+2) := by
  have h₁ := KS.W15.RationalMultiply.move_spec source work hsw s
  have h₂ := KS.W15.RationalMultiply.move_spec work target hwt
    (KS.W15.RationalMultiply.moveAfter source work s)
  have h := h₁.compose h₂
  have he : KS.W15.RationalMultiply.moveAfter work target
      (KS.W15.RationalMultiply.moveAfter source work s) =
      Function.update (Function.update s source []) target (s source) := by
    funext j
    by_cases hjs : j=source
    · subst j
      simp [KS.W15.RationalMultiply.moveAfter,hsw,hst,Function.update]
    · by_cases hjw : j=work
      · subst j
        simp [KS.W15.RationalMultiply.moveAfter,hwt,hw,Function.update]
      · by_cases hjt : j=target
        · subst j
          simp [KS.W15.RationalMultiply.moveAfter,hsw.symm,hst.symm,hwt.symm,
            hw,ht,Function.update]
        · simp [KS.W15.RationalMultiply.moveAfter,hjs,hjw,hjt,Function.update]
  rw [he] at h
  have hc : (s source).length+1+
      (KS.W15.RationalMultiply.moveAfter source work s work).length+1 =
      2*(s source).length+2 := by
    simp [KS.W15.RationalMultiply.moveAfter,hsw.symm,hw]
    omega
  simpa only [Nat.add_assoc] using (hc ▸ h)

end CurrentKS.CleanRoutine

end

end OAI
