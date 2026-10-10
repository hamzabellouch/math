import OAI.Analysis.KadisonSimilarity.Tensor.InvariantTensors
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-! Finite tensor matrices and the invariance of permutation contractions.
These coordinate calculations supply the spanning generators for the local
Schur--Weyl argument. -/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- The matrix of a tensor product of finitely many matrix operators. -/
def tupleTensorMatrix (v : ι → Matrix α α ℂ) : Matrix (ι → α) (ι → α) ℂ :=
  Matrix.of fun f g => ∏ i, v i (f i) (g i)

omit [DecidableEq ι] [Fintype α] [DecidableEq α] in
@[simp] theorem tupleTensorMatrix_apply (v : ι → Matrix α α ℂ) (f g : ι → α) :
    tupleTensorMatrix v f g = ∏ i, v i (f i) (g i) := rfl

omit [DecidableEq α] in
theorem tupleTensorMatrix_mul (v w : ι → Matrix α α ℂ) :
    tupleTensorMatrix (fun i => v i * w i) = tupleTensorMatrix v * tupleTensorMatrix w := by
  ext f g
  simp only [tupleTensorMatrix_apply, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum fun i a => v i (f i) a * w i a (g i)

omit [DecidableEq ι] [Fintype α] in
@[simp] theorem tupleTensorMatrix_one :
    tupleTensorMatrix (fun _ : ι => (1 : Matrix α α ℂ)) = 1 := by
  ext f g
  simp only [tupleTensorMatrix_apply, Matrix.one_apply, Fintype.prod_boole]
  congr 1
  exact propext funext_iff.symm

omit [DecidableEq ι] [Fintype α] [DecidableEq α] in
@[simp] theorem tupleTensorMatrix_star (v : ι → Matrix α α ℂ) :
    tupleTensorMatrix (fun i => star (v i)) = star (tupleTensorMatrix v) := by
  ext f g
  simp [tupleTensorMatrix, Matrix.star_apply]

/-- Reordering the tensor coordinates. -/
def tensorCoordinatePermutation (π : Equiv.Perm ι) : Equiv.Perm (ι → α) where
  toFun f := fun i => f (π i)
  invFun f := fun i => f (π.symm i)
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp

/-- Its matrix uses the same successor convention as `permutationContraction`. -/
def tensorPermutationMatrix (π : Equiv.Perm ι) : Matrix (ι → α) (ι → α) ℂ :=
  Matrix.of fun f g => if f = tensorCoordinatePermutation π g then 1 else 0

theorem tensorMatrix_mul_permutation (v : ι → Matrix α α ℂ) (π : Equiv.Perm ι)
    (f g : ι → α) :
    (tupleTensorMatrix v * tensorPermutationMatrix π : Matrix (ι → α) (ι → α) ℂ) f g =
      tupleTensorMatrix v f (tensorCoordinatePermutation π g) := by
  simp [Matrix.mul_apply, tensorPermutationMatrix]

theorem permutation_mul_tensorMatrix (v : ι → Matrix α α ℂ) (π : Equiv.Perm ι)
    (f g : ι → α) :
    (tensorPermutationMatrix π * tupleTensorMatrix v : Matrix (ι → α) (ι → α) ℂ) f g =
      tupleTensorMatrix v ((tensorCoordinatePermutation π).symm f) g := by
  simp [Matrix.mul_apply, tensorPermutationMatrix, ← Equiv.symm_apply_eq]

theorem constant_tensorMatrix_commutes_permutation (a : Matrix α α ℂ)
    (π : Equiv.Perm ι) :
    tupleTensorMatrix (fun _ : ι => a) * tensorPermutationMatrix π =
      tensorPermutationMatrix π * tupleTensorMatrix (fun _ : ι => a) := by
  ext f g
  rw [tensorMatrix_mul_permutation, permutation_mul_tensorMatrix]
  change (∏ i, a (f i) (g (π i))) = ∏ i, a (f (π.symm i)) (g i)
  simpa using Equiv.prod_comp π (fun i => a (f (π.symm i)) (g i))

theorem permutationContraction_eq_trace (π : Equiv.Perm ι)
    (v : ι → Matrix α α ℂ) :
    permutationContraction π v =
      Matrix.trace (tupleTensorMatrix v * tensorPermutationMatrix π) := by
  simp only [Matrix.trace, Matrix.diag, tensorMatrix_mul_permutation]
  rfl

/-- Simultaneous unitary conjugation preserves every permutation contraction. -/
theorem permutationContraction_unitary_conjugate (π : Equiv.Perm ι)
    (u : Matrix.unitaryGroup α ℂ) (v : ι → Matrix α α ℂ) :
    permutationContraction π (fun i =>
      (u : Matrix α α ℂ) * v i * star (u : Matrix α α ℂ)) =
        permutationContraction π v := by
  let U := tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ))
  have hU : star U * U = 1 := by
    rw [← tupleTensorMatrix_star, ← tupleTensorMatrix_mul]
    simpa only [Unitary.coe_star_mul_self] using (tupleTensorMatrix_one (ι := ι) (α := α))
  have hc : star U * tensorPermutationMatrix π = tensorPermutationMatrix π * star U := by
    simpa only [U, ← tupleTensorMatrix_star] using
      constant_tensorMatrix_commutes_permutation (star (u : Matrix α α ℂ)) π
  rw [permutationContraction_eq_trace, tupleTensorMatrix_mul, tupleTensorMatrix_mul,
    tupleTensorMatrix_star]
  change Matrix.trace (U * tupleTensorMatrix v * star U * tensorPermutationMatrix π) = _
  rw [Matrix.mul_assoc (U * _), hc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle,
    ← Matrix.mul_assoc (star U), hU, Matrix.one_mul]
  exact (permutationContraction_eq_trace π v).symm

theorem permutationContractionMultilinear_invariant (π : Equiv.Perm ι) :
    UnitaryConjugationInvariant (permutationContractionMultilinear (α := α) π) := by
  intro u v
  simpa only [permutationContractionMultilinear_apply] using
    permutationContraction_unitary_conjugate π u v

theorem normalizedPermutationMultilinear_invariant (π : Equiv.Perm ι) :
    UnitaryConjugationInvariant (normalizedPermutationMultilinear (α := α) π) := by
  intro u v
  simp only [normalizedPermutationMultilinear_apply, normalizedPermutationContraction,
    permutationContraction_unitary_conjugate]

end KadisonSimilarity

end

end OAI
