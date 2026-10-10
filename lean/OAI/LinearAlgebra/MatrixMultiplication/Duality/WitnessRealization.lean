import OAI.LinearAlgebra.MatrixMultiplication.Duality.FiniteRealization
import OAI.LinearAlgebra.MatrixMultiplication.Duality.FiniteRates
import OAI.LinearAlgebra.MatrixMultiplication.Duality.WitnessProgram
import OAI.LinearAlgebra.MatrixMultiplication.Completion.HierarchyPrograms
import OAI.LinearAlgebra.MatrixMultiplication.Completion.Termination

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitnessRealization

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLabels.TopologicalFlatten CompletionHierarchyWords
open scoped BigOperators Classical

theorem program_context (a : DualWitness.Support) : DualWitness.program.context a = PUnit.unit :=
  rfl

theorem program_joint :
    Function.Injective (fun a : DualWitness.Support =>
      (DualWitness.program.view .B a, DualWitness.program.view .C a,
        DualWitness.program.view .A a)) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact h

def hierarchy :
    ReadableHierarchy DualWitness.Support DualWitness.Word DualWitness.Word DualWitness.Word :=
  ReadableHierarchy.ofProgram DualWitness.program PUnit.unit program_context program_joint

theorem hierarchy_complete :
    Function.Injective (labelRecordOf hierarchy.labels hierarchy.depth) :=
  ReadableHierarchy.ofProgram_complete DualWitness.program PUnit.unit program_context
    program_joint DualWitness.program_complete

@[simp] theorem hierarchy_x (a : DualWitness.Support) : hierarchy.x a = a.val.val.1 := rfl
@[simp] theorem hierarchy_y (a : DualWitness.Support) : hierarchy.y a = a.val.val.2.1 := rfl
@[simp] theorem hierarchy_z (a : DualWitness.Support) : hierarchy.z a = a.val.val.2.2 := rfl

def tensor : Tensor ℂ DualWitness.Word DualWitness.Word DualWitness.Word :=
  CompletionTermination.tensor DualWitness.source .A

def retainedLeafEquiv : CompletionTermination.Leaf DualWitness.source .A ≃ DualWitness.Support :=
  CompletionTermination.retainedLeafEquiv DualWitness.source .A .B .C
    (by intro c; cases c <;> simp)

def approximation :
    Tensor.PolynomialApproximation tensor (2 ^ 288)
      (Script.dual.order 1) (Script.dual.degree 3) :=
  CompletionTermination.approximation DualWitness.source .A DualFiniteRealization.dualSource

theorem base_unit (x y z : Fin 2) (h : BaseTwo.tensor x y z ≠ 0) :
    BaseTwo.tensor x y z = 1 := by
  unfold BaseTwo.tensor at h ⊢
  split_ifs with hsum
  · rfl
  · simp [hsum] at h

theorem tensor_unit_coefficients (x y z : DualWitness.Word) (h : tensor x y z ≠ 0) :
    tensor x y z = 1 := by
  obtain ⟨hs, ha⟩ := (CompletionTermination.support_iff DualWitness.source .A x y z).mp h
  change (if ownerFlag DualWitness.source .A (coordinate (x, y, z) .A) then 0
    else DualWitness.source.tensor x y z) = 1
  rw [ite_eq_right ha]
  exact CompletionFiniteRealization.script_coefficient_one BaseTwo.flagged base_unit
    Script.dual x y z hs

theorem source_supported (x y z : DualWitness.Word) (h : tensor x y z ≠ 0) :
    ∃ a : DualWitness.Support, hierarchy.x a = x ∧ hierarchy.y a = y ∧ hierarchy.z a = z :=
  ⟨retainedLeafEquiv ⟨(x, y, z), h⟩, rfl, rfl, rfl⟩

theorem source_unit (a : DualWitness.Support) :
    tensor (hierarchy.x a) (hierarchy.y a) (hierarchy.z a) = 1 :=
  tensor_unit_coefficients _ _ _ (retainedLeafEquiv.symm a).property

def witness (counts : DualWitness.Support → ℕ) (t : ℕ) :
    ComplexWitness.FiniteRectangularWitness :=
  DualFiniteRealization.witness hierarchy counts t hierarchy_complete approximation
    (pow_pos (by decide : 0 < (2 : ℕ)) 288) source_supported source_unit

theorem witness_rank (counts : DualWitness.Support → ℕ) (t : ℕ) :
    (witness counts t).rank =
      (2 ^ (288 * CompletionFiniteRealization.blocks counts t) *
        StageHierarchyResources.stageAuxiliaryBudget counts hierarchy.labels hierarchy.depth t) ^ 2 := by
  rw [witness, DualFiniteRealization.witness_rank_stageBudget, ← pow_mul]

theorem source_log : Real.log ((2 ^ 288 : ℕ) : ℝ) = 288 * Real.log 2 := by
  rw [Nat.cast_pow, Real.log_pow]
  norm_num

theorem source_log_positive : 0 < Real.log ((2 ^ 288 : ℕ) : ℝ) := by
  rw [source_log]
  exact mul_pos (by norm_num) (Real.log_pos (by norm_num))

end MatrixMultiplication.DualWitnessRealization

end

end OAI
