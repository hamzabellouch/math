import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryMultiplySemantics
import OAI.Analysis.MatrixSigning.Machines.BinaryExpressionEvaluator
import OAI.Analysis.MatrixSigning.Arithmetic.RationalAddPorts
import OAI.Analysis.MatrixSigning.Arithmetic.RationalSubtractPorts
import OAI.Analysis.MatrixSigning.Arithmetic.RationalSignPorts
import OAI.Analysis.MatrixSigning.Machines.BinaryFloorBridge
import OAI.Analysis.MatrixSigning.Matrices.PivotHistoryBounds
import OAI.Analysis.MatrixSigning.Matrices.SavedPivotStack
import OAI.Analysis.MatrixSigning.Potential.EnsembleForcesNegative
import OAI.Analysis.MatrixSigning.Complexity.PolynomialCoordinates
import OAI.Analysis.MatrixSigning.Complexity.PolynomialRoundedStep
import OAI.Analysis.MatrixSigning.Complexity.PolynomialCurvature
import OAI.Analysis.MatrixSigning.Complexity.PolynomialMatrixSum
import OAI.Analysis.MatrixSigning.Complexity.PolynomialVariance
import OAI.Analysis.MatrixSigning.Complexity.PolynomialOriginalFields
import OAI.Analysis.MatrixSigning.Realization.OriginalMachine
import OAI.Analysis.MatrixSigning.Complexity.PolynomialOriginalOutput

namespace OAI

section

namespace CurrentKS
open Realization

theorem originalMachine_polynomial : ∃ C degree : ℕ,0<C ∧ ∀ x,Admissible x →
    originalMachineTicks x≤C*(x.length+1)^degree := by
  have h := runsPoly_originalSigning (fun x : {x : Input // Admissible x} => x.val)
    (isPoly_self (fun x : {x : Input // Admissible x} => x.val.length)) (fun x => x.property)
  obtain ⟨p,hp⟩ := h.cost
  refine ⟨p.coefficient+1,p.degree,Nat.succ_pos _,?_⟩
  intro x hx
  exact ((hp ⟨x,hx⟩).trans (p.eval_le_input_polynomial x.length)).trans
    (Nat.mul_le_mul_right _ (Nat.le_succ p.coefficient))

theorem deterministic_rank_one_signing : DeterministicRankOneSigning :=
  deterministic_of_original_cost originalMachine_polynomial

end CurrentKS

end

end OAI
