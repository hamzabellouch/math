import OAI.Combinatorics.ContingencyTables.Machines.LiteralProgram
import OAI.Combinatorics.ContingencyTables.Machines.MatrixEncoding
import OAI.Combinatorics.ContingencyTables.Sampling.ProfilePublicMachine

namespace OAI

/-! # Packed physical output still identifies its contingency table -/

namespace ContingencyTables.PackedMatrixInjective
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing

lemma deterministic_unique (P : Program) (input X Y : Tape Symbol) (n m : ℕ)
    (hX : P.Realizes input (.done X) n) (hY : P.Realizes input (.done Y) m) : X=Y := by
  obtain ⟨p,hp,hpm,_⟩ := hX
  obtain ⟨q,hq,hqm,_⟩ := hY
  have ha : p.All (fun T => T=X) := Experiment.all_of_mean_eq hpm _ rfl
  have hb : q.All (fun T => T=Y) := Experiment.all_of_mean_eq hqm _ rfl
  have he := hp.padded_execution (fun _ => rfl) (p.cost+q.cost) (Nat.le_add_right _ _) (fun _ => false)
  have hf := hq.padded_execution (fun _ => rfl) (p.cost+q.cost) (Nat.le_add_left _ _) (fun _ => false)
  rw [Experiment.all_run p _ ha] at he
  rw [Experiment.all_run q _ hb] at hf
  exact congrArg Cfg.tape (he.symm.trans hf)

lemma table_injective {m n : ℕ} {r : Fin m → ℕ} {c : Fin n → ℕ} (X Y : Table r c)
    (h : Tape.mk₁ (TreePost.packed (GreedyFeasibleTable.printMatrix (DensePrograms.matrixCode X.val)))=
      Tape.mk₁ (TreePost.packed (GreedyFeasibleTable.printMatrix (DensePrograms.matrixCode Y.val)))) : X=Y := by
  have hx := LiteralProgram.post_realizes (GreedyFeasibleTable.printMatrix (DensePrograms.matrixCode X.val))
    (ProfilePrograms.printMatrix_alphabet _)
  have hy := LiteralProgram.post_realizes (GreedyFeasibleTable.printMatrix (DensePrograms.matrixCode Y.val))
    (ProfilePrograms.printMatrix_alphabet _)
  rw [←h] at hy
  have ht := deterministic_unique LiteralProgram.post _ _ _ _ _ hx hy
  have he := congrArg Tape.right₀ ht
  simp only [Tape.mk₁,Tape.mk₂,Tape.mk'_right₀,DensePrograms.matrixCode,GreedyFeasibleTable.printMatrix_ofFn] at he
  exact Subtype.ext (Algorithms.blankMatrix_injective X.val Y.val he)

end ContingencyTables.PackedMatrixInjective

end OAI
