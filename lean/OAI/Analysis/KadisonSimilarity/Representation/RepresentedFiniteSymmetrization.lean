import OAI.Analysis.KadisonSimilarity.Tracial.FiniteFactorSymmetrization
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

namespace OAI

/-! # Finite matrix averaging in a fixed represented algebra

The scalar bound is supplied on the source C-star algebra. Actual normalized
Haar measures on the finite matrix-unitary groups produce a single operator
commuting with every stage. No von Neumann closure or independently chosen
invariant operator is needed in this step.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A norm perturbation by `δ` changes a source-algebra scalar commutator
bound `δ` into at most `3δ`. -/
theorem represented_scalar_bound_of_close
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Y₀ Y : H →L[ℂ] H)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (σ a)‖ ≤ δ * ‖a‖)
    (hclose : ‖Y₀ - Y‖ ≤ δ) :
    ∀ a, ‖commutator Y₀ (σ a)‖ ≤ (3 * δ) * ‖a‖ := by
  intro a
  calc
    ‖commutator Y₀ (σ a)‖ ≤ δ * ‖a‖ + 2 * δ * ‖σ a‖ :=
      norm_commutator_le_of_approx Y₀ Y (σ a) (hscalar a) hclose
    _ ≤ δ * ‖a‖ + 2 * δ * ‖a‖ := by
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le σ a
    _ = (3 * δ) * ‖a‖ := by ring

private theorem norm_matrixUnitary_image_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] A) (u : Matrix.unitaryGroup α ℂ) :
    ‖ι (u : Matrix α α ℂ)‖ ≤ 1 := by
  let v := Unitary.map (StarMonoidHom.ofClass ι) u
  have h : ‖(v : A)‖ = ‖(1 : A)‖ := by
    simpa only [mul_one] using CStarRing.norm_coe_unitary_mul v (1 : A)
  change ‖(v : A)‖ ≤ 1
  rw [h]
  exact IsStarProjection.norm_le 1 (.one A)

variable {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]

attribute [local instance] finiteMatrixUnitaryCompactSpace
  finiteMatrixUnitaryMeasurableSpace finiteMatrixUnitaryBorelSpace

/-- Actual Haar averages and a weak-operator cluster point give the finite
factor's initial perturbation. The scalar norm is measured on the original
source algebra; the bound and the distance do not depend on matrix sizes. -/
theorem exists_represented_finite_matrix_symmetrization
    [∀ n, Nonempty (I n)]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ι : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (transition : ∀ n m, n ≤ m →
      Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (hcompat : ∀ n m h a, ι m (transition n m h a) = ι n a)
    (Y : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (σ a)‖ ≤ δ * ‖a‖) :
    ∃ Y₀ : H →L[ℂ] H, ‖Y₀‖ ≤ ‖Y‖ ∧ ‖Y₀ - Y‖ ≤ δ ∧
      (∀ a, ‖commutator Y₀ (σ a)‖ ≤ (3 * δ) * ‖a‖) ∧
      ∀ n a, commutator Y₀ (σ (ι n a)) = 0 := by
  let R := fun n => σ.comp (ι n)
  let U := fun n => matrixUnitaryAction (R n)
  let emb := fun n m h => Unitary.map (StarMonoidHom.ofClass (transition n m h))
  have hc n m h u : U m (emb n m h u) = U n u :=
    congrArg σ (hcompat n m h (u : Matrix (I n) (I n) ℂ))
  have hI n : WeaklyIntegrable (finiteMatrixHaarProbability (I := I) n)
      (unitaryConjugate (U n) Y) :=
    weaklyIntegrable_unitaryConjugate _ _ (matrixUnitaryAction_adjoint (R n))
      (matrixUnitaryAction_continuous (R n)) Y
  have hcomm n u : ‖commutator Y (U n u)‖ ≤ δ :=
    (hscalar (ι n (u : Matrix (I n) (I n) ℂ))).trans
      (mul_le_of_le_one_right hδ (norm_matrixUnitary_image_le_one (ι n) u))
  obtain ⟨Y₀, hnorm, hclose, hinv⟩ := exists_simultaneously_symmetrized_close
    (finiteMatrixHaarProbability (I := I)) U
    (fun n => matrixUnitaryAction_norm_le (R n)) (fun n m h u => emb n m h u) hc Y hI hδ hcomm
  refine ⟨Y₀, hnorm, hclose, represented_scalar_bound_of_close σ Y₀ Y hδ hscalar hclose, ?_⟩
  intro n a
  exact commutes_matrix_of_unitaries (R n) Y₀ (hinv n) a

end KadisonSimilarity

end

end OAI
