import Mathlib
import OAI.Analysis.MatrixSigning.Realization.NaturalRealization
import OAI.Analysis.MatrixSigning.Machines.SchurCounters

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

abbrev binaryNatCode : ℕ → Word := Computability.encodeNat

def binarySucc : Realizes binaryNatCode binaryNatCode Nat.succ where
  cost := fun n => 2*(binaryNatCode n).length+6
  routine := {
    scratch := 2
    program := KS.W07.SchurCounters.incrementProgram ⟨![1,0,2],by decide⟩
    spec := fun n => by
      have h := KS.W07.SchurCounters.increment_spec
        (⟨![1,0,2],by decide⟩ : Fin 3 ↪ Fin 3) (io (binaryNatCode n)) n rfl rfl rfl
      have he : Function.update (io (binaryNatCode n)) (0 : Fin 3)
          (Computability.encodeNat (n+1))=io (binaryNatCode (n+1)) := by
        funext j;fin_cases j <;> rfl
      change KS.W03.MachineCombinators.RunSpec _ _
        (Function.update (io (binaryNatCode n)) (0 : Fin 3)
          (Computability.encodeNat (n+1))) _ at h
      rw [he] at h
      exact h }

def natToBinary : Realizes natCode binaryNatCode id :=
  (((identity natCode).both (constant natCode binaryNatCode 0)).then binarySucc.iterate).congr (by
    intro n
    change Nat.succ^[n] 0=n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',ih])

end CurrentKS.Realization

end

end OAI
