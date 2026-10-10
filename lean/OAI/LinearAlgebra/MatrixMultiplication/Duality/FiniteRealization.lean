import OAI.LinearAlgebra.MatrixMultiplication.Completion.FiniteRealization
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.MatrixBalancing
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexWitness
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.BaseTensorBudgets

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualFiniteRealization

open MatrixMultiplication.Foundation RecursiveCompletion
open CompletionHierarchyWords CompletionExecution CompletionFiniteRealization
open scoped BigOperators Classical

variable {A X Y Z : Type} [Fintype A]
variable (H : ReadableHierarchy A X Y Z) (counts : A → ℕ) (t : ℕ)
variable (complete : Function.Injective (labelRecordOf H.labels H.depth))
variable [Fintype X] [Fintype Y] [Fintype Z]

def rankBudget (R : ℕ) : ℕ :=
  R ^ CompletionFiniteRealization.blocks counts t * (realize H counts t).execution.rankBound

def sourcePower {T : Tensor ℂ X Y Z} {R d D : ℕ}
    (source : Tensor.PolynomialApproximation T R d D) :
    Tensor.PolynomialApproximation
      (Tensor.power T (CompletionFiniteRealization.blocks counts t))
      (R ^ CompletionFiniteRealization.blocks counts t)
      (d * CompletionFiniteRealization.blocks counts t)
      (D * CompletionFiniteRealization.blocks counts t) :=
  source.power (CompletionFiniteRealization.blocks counts t)

def approximation {T : Tensor ℂ X Y Z} {R d D : ℕ}
    (source : Tensor.PolynomialApproximation T R d D)
    (supported : ∀ x y z, T x y z ≠ 0 → ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
    (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1) :
    Tensor.PolynomialApproximation
      (Tensor.directSum (fun _ : Fin (copies H counts t) =>
        Tensor.matrixCoefficients (K := ℂ)
          (Fin (rows H counts t)) (Fin (inner H counts t)) (Fin (columns H counts t))))
      (rankBudget H counts t R) (order H counts t d) (degree H counts t D) := by
  have hs : ∀ x y z, ¬ support H counts t x y z →
      Tensor.power T (CompletionFiniteRealization.blocks counts t) x y z = 0 := by
    intro x y z outside
    by_contra nonzero
    apply outside
    intro i
    exact supported _ _ _ ((Finset.prod_ne_zero_iff.mp nonzero) i (Finset.mem_univ i))
  have full := ExecutionApproximation.approximation (realize H counts t).execution
    (sourcePower counts t source) hs
  have selected := full.pullback (leftSelect H counts t complete)
    (middleSelect H counts t complete) (rightSelect H counts t complete)
  rw [selected_output H counts t complete T unit] at selected
  exact selected

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem rankBudget_pos {R : ℕ} (hR : 0 < R) : 0 < rankBudget H counts t R :=
  Nat.mul_pos (pow_pos hR _) (auxiliaryRank_pos H counts t)

def witness {T : Tensor ℂ X Y Z} {R d D : ℕ}
    (source : Tensor.PolynomialApproximation T R d D) (hR : 0 < R)
    (supported : ∀ x y z, T x y z ≠ 0 → ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
    (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1) :
    ComplexWitness.FiniteRectangularWitness where
  outer := rows H counts t * inner H counts t
  inner := columns H counts t ^ 2
  multiplicity := copies H counts t ^ 2
  rank := rankBudget H counts t R ^ 2
  outer_pos := Nat.mul_pos (dimensions_positive H counts t).1
    (dimensions_positive H counts t).2.1
  inner_pos := pow_pos (dimensions_positive H counts t).2.2 2
  multiplicity_pos := pow_pos (copies_pos H counts t complete) 2
  rank_pos := pow_pos (rankBudget_pos H counts t hR) 2
  order := 2 * order H counts t d
  degree := 2 * degree H counts t D
  approximation := MatrixBalancing.finiteBalanced
    (approximation H counts t complete source supported unit)

section Projections

variable {T : Tensor ℂ X Y Z} {R d D : ℕ}
variable (source : Tensor.PolynomialApproximation T R d D) (hR : 0 < R)
variable (supported : ∀ x y z, T x y z ≠ 0 → ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
variable (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1)

@[simp] theorem witness_outer :
    (witness H counts t complete source hR supported unit).outer =
      rows H counts t * inner H counts t := rfl

@[simp] theorem witness_inner :
    (witness H counts t complete source hR supported unit).inner = columns H counts t ^ 2 := rfl

@[simp] theorem witness_multiplicity :
    (witness H counts t complete source hR supported unit).multiplicity = copies H counts t ^ 2 :=
  rfl

@[simp] theorem witness_rank :
    (witness H counts t complete source hR supported unit).rank =
      (R ^ CompletionFiniteRealization.blocks counts t *
        (realize H counts t).execution.rankBound) ^ 2 := rfl

theorem witness_dimensions :
    (witness H counts t complete source hR supported unit).outer =
      ConditionalLabels.stagePairingSize counts H.labels H.depth
        (fun n => H.pair n.val) .xz t *
      ConditionalLabels.stagePairingSize counts H.labels H.depth
        (fun n => H.pair n.val) .xy t ∧
    (witness H counts t complete source hR supported unit).inner =
      ConditionalLabels.stagePairingSize counts H.labels H.depth
        (fun n => H.pair n.val) .yz t ^ 2 := by
  rcases realize_dimensions H counts t with ⟨hr, hi, hc⟩
  change (realize H counts t).shape.rows * (realize H counts t).shape.inner = _ ∧
    (realize H counts t).shape.columns ^ 2 = _
  simp only [hr, hi, hc, and_self]

theorem witness_rank_stageBudget :
    (witness H counts t complete source hR supported unit).rank =
      (R ^ CompletionFiniteRealization.blocks counts t *
        StageHierarchyResources.stageAuxiliaryBudget counts H.labels H.depth t) ^ 2 := by
  rw [witness_rank, realize_rankBound]

end Projections

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem rankBudget_base (base factors : ℕ) :
    rankBudget H counts t (base ^ factors) =
      base ^ (factors * CompletionFiniteRealization.blocks counts t) *
        StageHierarchyResources.stageAuxiliaryBudget counts H.labels H.depth t := by
  simp only [rankBudget, ← pow_mul, realize_rankBound]

def dualSource :
    Tensor.PolynomialApproximation (Script.tensor BaseTwo.flagged Script.dual).tensor
      (2 ^ 288) (Script.dual.order 1) (Script.dual.degree 3) := by
  simpa only [Script.dual_factors] using
    Script.approximation BaseTwo.flagged BaseTwo.approximation Script.dual

end MatrixMultiplication.DualFiniteRealization

end

end OAI
