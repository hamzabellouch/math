import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedBranch
import OAI.Analysis.MatrixSigning.Machines.FixedRun
import OAI.Analysis.MatrixSigning.Realization.PairRoutine

namespace OAI

namespace CurrentKS.ConditionalRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine KS.W29.FixedBranch

abbrev flag (n : ℕ) : Fin (n+3) := ⟨n+1,by omega⟩
abbrev work (n : ℕ) : Fin (n+3) := ⟨n+2,by omega⟩
def ports (n : ℕ) : Fin (n+1) ↪ Fin (n+3) := ⟨Fin.castAdd 2,Fin.castAdd_injective _ _⟩
def parsePorts (n : ℕ) : Fin 3 ↪ Fin (n+3) :=
  ⟨![0,flag n,work n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩
@[simp] private lemma parsePorts_apply (n : ℕ) (i : Fin 3) :
    parsePorts n i = ![0,flag n,work n] i := rfl

def state (n : ℕ) (w : Word) (b : Bool) : Fin (n+3) → Word :=
  fun j => if j.val=0 then w else if j.val=n+1 then [b] else []
def parse (n : ℕ) : Program (n+3) := KS.W11.FrameWireCodec.unframeProgram (parsePorts n)
def select (n : ℕ) (heads : Fin (n+3) → Fin 3) (_ : Bool) : SelectInstruction (n+3) :=
  ⟨if heads (flag n)=2 then .left else .right,
    Vector.ofFn (fun j => if j=flag n then .pop else .stay)⟩

def choose (n : ℕ) (P Q : Program (n+1)) : Program (n+3) :=
  branch (liftPorts P (ports n)) (liftPorts Q (ports n)) 0 (select n)

def program (n : ℕ) (P Q : Program (n+1)) : Program (n+3) := compose (parse n) (choose n P Q)

lemma parse_spec (n : ℕ) (w : Word) (b : Bool) :
    RunSpec (parse n) (io (PairRoutine.pair [b] w)) (state n w b) 5 := by
  have h := KS.W11.FrameWireCodec.unframe_spec (parsePorts n) (fun _ => []) [b] w
  convert h using 1 <;> (try rfl) <;> funext j <;>
    simp only [KS.W28.FixedPositiveSerializer.registers,parsePorts_apply] <;>
    dsimp [state,io] <;>
    simp only [Fin.ext_iff] <;> split_ifs <;> simp_all

lemma choose_true (n : ℕ) (P Q : Program (n+3)) (w out : Word) (cost : ℕ)
    (h : RunSpec P (io w) (io out) cost) :
    RunSpec (branch P Q 0 (select n)) (state n w true) (io out) (cost+1) := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin tail =>
    have ht : tail.length=cost := by simpa using hbits
    have hs : (branch P Q 0 (select n)).toMachine.step
        ⟨some (start P Q),state n w true⟩ coin =
        KS.W29.FixedBranch.liftLeft P Q ⟨some P.initial,io w⟩ := by
      rw [step_start]
      apply KS.W19.FixedRun.config_ext
      · simp [select,observedHeads,state,flag,KS.W29.topCode,selectInstruction,KS.W29.FixedBranch.liftLeft]
      · intro j
        simp only [select,selectInstruction,KS.W01.FixedStack.Instruction.action,Vector.getElem_ofFn]
        dsimp [KS.W29.FixedBranch.liftLeft]
        by_cases hj : j=flag n
        · subst j;simp [state,io,flag,KS.W29.StackAction.apply]
        · have hjv : j.val≠n+1 := by simpa [Fin.ext_iff,flag] using hj
          simp [hj,KS.W29.StackAction.apply]
          dsimp only [state,io]
          simp [hjv]
    change (branch P Q 0 (select n)).toMachine.run
      ⟨some (start P Q),state n w true⟩ (coin::tail)=_
    rw [KS.W01.FixedStack.Machine.run,hs,run_left]
    erw [h tail ht]
    rfl

lemma choose_false (n : ℕ) (P Q : Program (n+3)) (w out : Word) (cost : ℕ)
    (h : RunSpec Q (io w) (io out) cost) :
    RunSpec (branch P Q 0 (select n)) (state n w false) (io out) (cost+1) := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin tail =>
    have ht : tail.length=cost := by simpa using hbits
    have hs : (branch P Q 0 (select n)).toMachine.step
        ⟨some (start P Q),state n w false⟩ coin =
        KS.W29.FixedBranch.liftRight P Q ⟨some Q.initial,io w⟩ := by
      rw [step_start]
      apply KS.W19.FixedRun.config_ext
      · simp [select,observedHeads,state,flag,KS.W29.topCode,selectInstruction,KS.W29.FixedBranch.liftRight]
      · intro j
        simp only [select,selectInstruction,KS.W01.FixedStack.Instruction.action,Vector.getElem_ofFn]
        dsimp [KS.W29.FixedBranch.liftRight]
        by_cases hj : j=flag n
        · subst j;simp [state,io,flag,KS.W29.StackAction.apply]
        · have hjv : j.val≠n+1 := by simpa [Fin.ext_iff,flag] using hj
          simp [hj,KS.W29.StackAction.apply]
          dsimp only [state,io]
          simp [hjv]
    change (branch P Q 0 (select n)).toMachine.run
      ⟨some (start P Q),state n w false⟩ (coin::tail)=_
    rw [KS.W01.FixedStack.Machine.run,hs,run_right]
    erw [h tail ht]
    rfl

lemma core_spec (n : ℕ) (P : Program (n+1)) (w out : Word) (cost : ℕ)
    (h : RunSpec P (io w) (io out) cost) :
    RunSpec (liftPorts P (ports n)) (io w) (io out) cost := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ h
  · intro j;rfl
  · intro j;rfl
  · intro j hj
    have hz : j.val≠0 := by intro hz;exact hj 0 (Fin.ext hz)
    simp [io,hz]

variable {α : Type*} {encode yes no : α → Word} {c d : α → ℕ}
def routine (r : Routine encode yes c) (s : Routine encode no d) :
    Routine (fun p : Bool×α => PairRoutine.pair [p.1] (encode p.2))
      (fun p => if p.1 then yes p.2 else no p.2)
      (fun p => 5+(if p.1 then c p.2 else d p.2)+1) :=
  let n := r.scratch+s.scratch
  let r' := r.pad n (Nat.le_add_right _ _)
  let s' := s.pad n (Nat.le_add_left _ _)
  { scratch := n+2
    program := program n r'.program s'.program
    spec := fun p => by
      obtain ⟨b,x⟩ := p
      cases b
      · have h := (parse_spec n (encode x) false).compose
          (choose_false n (liftPorts r'.program (ports n)) _ _ _ _ (core_spec n _ _ _ _ (s'.spec x)))
        simp only [Bool.false_eq_true,ite_false,Nat.add_assoc] at h ⊢
        exact h
      · have h := (parse_spec n (encode x) true).compose
          (choose_true n _ (liftPorts s'.program (ports n)) _ _ _ (core_spec n _ _ _ _ (r'.spec x)))
        simp only [ite_true,Nat.add_assoc] at h ⊢
        exact h }

end CurrentKS.ConditionalRoutine

end OAI
