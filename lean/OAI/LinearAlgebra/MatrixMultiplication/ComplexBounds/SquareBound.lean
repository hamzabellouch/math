import OAI.LinearAlgebra.MatrixMultiplication.Entropy.BaseConditionalReaders
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Compatibility
import OAI.LinearAlgebra.MatrixMultiplication.Completion.HierarchyPrograms
import OAI.LinearAlgebra.MatrixMultiplication.Completion.SquareRates
import OAI.LinearAlgebra.MatrixMultiplication.ComplexBounds.SquareCounts

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.SquareBound

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLabels.TopologicalFlatten CompletionHierarchyWords Filter
open scoped BigOperators Topology Classical

abbrev Coordinate := Script.Coord (Fin 3) Script.square
abbrev Carrier := RetainedLeaf SquareCounts.completed .B .C

def conditional : ReadableTensor SquareCounts.completed :=
  ReadableTensor.script BaseThree.flagged BaseConditionalReaders.baseThreeReadable Script.square

def program :
    Program Carrier (CompletionLabels.Coordinate Coordinate Coordinate Coordinate)
      PUnit (Color ⊕ conditional.Code) (1 + conditional.depth) :=
  terminationProgram SquareCounts.completed .B .C (by decide)
    conditional.program conditional.context_eq conditional.view_eq

theorem program_context (a : Carrier) : program.context a = PUnit.unit := rfl

theorem program_view (side : Color) (a : Carrier) :
    program.view side a = coordinate a.val.val side := rfl

theorem program_joint :
    Function.Injective (fun a : Carrier => (program.view .B a, program.view .C a,
      program.view .A a)) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact h

def hierarchy : ReadableHierarchy Carrier Coordinate Coordinate Coordinate :=
  ReadableHierarchy.ofProgram program PUnit.unit program_context program_joint

theorem hierarchy_complete :
    Function.Injective (labelRecordOf hierarchy.labels hierarchy.depth) := by
  apply ReadableHierarchy.ofProgram_complete program PUnit.unit program_context program_joint
  exact terminationProgram_complete SquareCounts.completed .B .C (by decide)
    conditional.program conditional.context_eq conditional.view_eq conditional.complete

@[simp] theorem hierarchy_x (a : Carrier) : hierarchy.x a = a.val.val.1 := rfl
@[simp] theorem hierarchy_y (a : Carrier) : hierarchy.y a = a.val.val.2.1 := rfl
@[simp] theorem hierarchy_z (a : Carrier) : hierarchy.z a = a.val.val.2.2 := rfl

theorem source_supported (x y z : Coordinate) (h : SquareCounts.tensor x y z ≠ 0) :
    ∃ a : Carrier, hierarchy.x a = x ∧ hierarchy.y a = y ∧ hierarchy.z a = z := by
  exact ⟨SquareCounts.retainedLeafEquiv ⟨(x, y, z), h⟩, rfl, rfl, rfl⟩

theorem source_unit (a : Carrier) :
    SquareCounts.tensor (hierarchy.x a) (hierarchy.y a) (hierarchy.z a) = 1 := by
  exact SquareCounts.tensor_unit_coefficients _ _ _
    (SquareCounts.retainedLeafEquiv.symm a).property

def counts (_ : Carrier) : ℕ := 1

theorem card_carrier : Fintype.card Carrier = SquareCounts.leafCount :=
  (Fintype.card_congr SquareCounts.retainedLeafEquiv.symm).trans SquareCounts.card_leaf

theorem total_counts : (∑ a : Carrier, counts a) = SquareCounts.leafCount := by
  exact (Finset.card_eq_sum_ones Finset.univ).symm.trans card_carrier

theorem total_counts_pos : 0 < ∑ a : Carrier, counts a := by
  rw [total_counts]
  exact SquareCounts.leafCount_pos

theorem count_entropy :
    finiteEntropy (CompletionSquareRates.countMass counts) = Real.log SquareCounts.leafCount := by
  have hm : CompletionSquareRates.countMass counts = SquareCounts.retainedUniformLaw.mass := by
    funext a
    rw [SquareCounts.retainedUniformLaw_mass]
    rw [CompletionSquareRates.countMass, total_counts]
    simp only [counts, Nat.cast_one, one_div]
  rw [hm, SquareCounts.retainedUniformLaw_entropy]

def family (n : ℕ) : FiniteMMRealization :=
  CompletionSquareRates.positiveRealization hierarchy counts total_counts_pos
    hierarchy_complete SquareCounts.approximation source_supported source_unit (by decide) n

theorem score_limit (β : ℝ) :
    Tendsto (fun n => (family n).rates.score β) atTop
      (𝓝 (β / 216 * Real.log SquareWitness.leafCount)) := by
  have h := CompletionSquareRates.score_limit hierarchy counts total_counts_pos
    hierarchy_complete SquareCounts.approximation source_supported source_unit (by decide) β
  rw [count_entropy] at h
  convert h using 1 <;> norm_num [family, SquareCounts.leafCount, SquareWitness.leafCount]

theorem omega_lt_2267_div_1000 :
    MatrixMultiplication.Foundation.Arithmetic.omega < (2267 : ℝ) / 1000 :=
  SquareWitness.omega_lt_of_certified_uniform_square_family family
    (score_limit ((2267 : ℝ) / 1000))

theorem complex_omega_lt_2267_div_1000 :
    MatrixMultiplication.Arithmetic.omega ℂ < (2267 : ℝ) / 1000 := by
  rw [MatrixMultiplication.Arithmetic.complex_omega_eq]
  exact omega_lt_2267_div_1000

end MatrixMultiplication.SquareBound

end

end OAI
