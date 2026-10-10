import OAI.Combinatorics.ContingencyTables.Transport.QuadraticTransport
import Mathlib.LinearAlgebra.Matrix.BilinearForm

namespace OAI

/-!
# The two-level laminar kernel in contingency-table weights

The factor groups in the sampling paper's laminar-signature lemma are line
coordinate sets, with one nested small-slot subset in each line. Row and
column coordinates belong to separate lines. The normalized kernel
decomposition gives the quadratic one-positive-direction property.
-/

namespace ContingencyTables

open scoped BigOperators
open LinearMap (BilinForm)

section TwoLevel

variable {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]

/-- The normalized two-removal kernel: line factors and the nested small
coordinate factor are the only factors shared by two distinct indices. -/
def twoLevelKernel (line : I → G) (inner : I → Bool) (γ δ : G → ℝ) :
    Matrix I I ℝ := fun i j =>
  if line i = line j then
    γ (line i) * (if inner i = true ∧ inner j = true then δ (line i) else 1)
  else 1

/-- Indicator of one line-coordinate group. -/
def lineVector (line : I → G) (g : G) (i : I) : ℝ :=
  if line i = g then 1 else 0

/-- Indicator of the small-coordinate subgroup of one line. -/
def innerVector (line : I → G) (inner : I → Bool) (g : G) (i : I) : ℝ :=
  if line i = g ∧ inner i = true then 1 else 0

/-- The rank-one matrix associated with a vector. -/
def outerMatrix (v : I → ℝ) : Matrix I I ℝ := fun i j => v i * v j

/-- The linear sum of the coordinates weighted by `v`. -/
def vectorSum (v : I → ℝ) : (I → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i, v i • LinearMap.proj i

omit [DecidableEq I] in
lemma vectorSum_apply (v x : I → ℝ) : vectorSum v x = ∑ i, v i * x i := by
  simp [vectorSum]

lemma outerMatrix_form (v x y : I → ℝ) :
    (outerMatrix v).toBilin' x y = vectorSum v x * vectorSum v y := by
  rw [Matrix.toBilin'_apply, vectorSum_apply, vectorSum_apply]
  simp only [outerMatrix]
  have hprod (i j : I) : x i * (v i * v j) * y j = (v i * x i) * (v j * y j) := by
    ring
  simp_rw [hprod, ← Finset.mul_sum]
  rw [← Finset.sum_mul]

omit [Fintype I] [DecidableEq I] in
/-- The precise rank-one-minus-blocks identity for the line/inner family. -/
theorem twoLevelKernel_decomposition (line : I → G) (inner : I → Bool) (γ δ : G → ℝ) :
    twoLevelKernel line inner γ δ =
      outerMatrix (fun _ : I => 1) -
        ∑ g, ((1 - γ g) • outerMatrix (lineVector line g) +
          (γ g * (1 - δ g)) • outerMatrix (innerVector line inner g)) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, outerMatrix]
  rw [Finset.sum_eq_single (line i)]
  · by_cases hline : line i = line j
    · by_cases hi : inner i = true <;> by_cases hj : inner j = true <;>
        simp [twoLevelKernel, lineVector, innerVector, hline, hi, hj]
      all_goals ring
    · have hline' : line j ≠ line i := Ne.symm hline
      simp [twoLevelKernel, lineVector, innerVector, hline, hline']
  · intro g _ hg
    have hg' : line i ≠ g := Ne.symm hg
    simp [lineVector, innerVector, hg']
  · simp

/-- The corresponding bilinear decomposition makes the squares explicit
when both arguments are equal. -/
theorem twoLevelKernel_form (line : I → G) (inner : I → Bool) (γ δ : G → ℝ)
    (x y : I → ℝ) :
    (twoLevelKernel line inner γ δ).toBilin' x y =
      vectorSum (fun _ : I => 1) x * vectorSum (fun _ : I => 1) y -
        ∑ g, ((1 - γ g) * (vectorSum (lineVector line g) x * vectorSum (lineVector line g) y) +
          (γ g * (1 - δ g)) *
            (vectorSum (innerVector line inner g) x * vectorSum (innerVector line inner g) y)) := by
  rw [twoLevelKernel_decomposition]
  simp only [map_sub, map_sum, map_add, map_smul, LinearMap.sub_apply,
    LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    outerMatrix_form]

/-- The line/inner two-removal kernel has positive inertia at most one in
quadratic-form language. Its proof uses the actual matrix decomposition. -/
theorem twoLevelKernel_onePositive (line : I → G) (inner : I → Bool) (γ δ : G → ℝ)
    (hγ0 : ∀ g, 0 ≤ γ g) (hγ1 : ∀ g, γ g ≤ 1) (hδ1 : ∀ g, δ g ≤ 1) :
    OnePositiveDirection (twoLevelKernel line inner γ δ).toBilin' := by
  refine onePositiveDirection_of_kernel _ ?_ (vectorSum (fun _ : I => 1)) ?_
  · intro x y
    rw [twoLevelKernel_form, twoLevelKernel_form]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro g _
      ring
  · intro v hv
    rw [twoLevelKernel_form, hv, zero_mul, zero_sub]
    apply neg_nonpos.mpr
    apply Finset.sum_nonneg
    intro g _
    apply add_nonneg
    · exact mul_nonneg (sub_nonneg.mpr (hγ1 g)) (mul_self_nonneg _)
    · exact mul_nonneg (mul_nonneg (hγ0 g) (sub_nonneg.mpr (hδ1 g))) (mul_self_nonneg _)

/-- The bilinear kernel is symmetric even before positivity assumptions. -/
lemma twoLevelKernel_form_symm (line : I → G) (inner : I → Bool) (γ δ : G → ℝ)
    (x y : I → ℝ) :
    (twoLevelKernel line inner γ δ).toBilin' x y =
      (twoLevelKernel line inner γ δ).toBilin' y x := by
  rw [twoLevelKernel_form, twoLevelKernel_form]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro g _
    ring

/-- The normalized kernel is nonpositive on the zero-sum hyperplane. -/
theorem twoLevelKernel_nonpositive (line : I → G) (inner : I → Bool) (γ δ : G → ℝ)
    (hγ0 : ∀ g, 0 ≤ γ g) (hγ1 : ∀ g, γ g ≤ 1) (hδ1 : ∀ g, δ g ≤ 1)
    (v : I → ℝ) (hv : vectorSum (fun _ : I => 1) v = 0) :
    (twoLevelKernel line inner γ δ).toBilin' v v ≤ 0 := by
  rw [twoLevelKernel_form, hv, zero_mul, zero_sub]
  apply neg_nonpos.mpr
  apply Finset.sum_nonneg
  intro g _
  apply add_nonneg
  · exact mul_nonneg (sub_nonneg.mpr (hγ1 g)) (mul_self_nonneg _)
  · exact mul_nonneg (mul_nonneg (hγ0 g) (sub_nonneg.mpr (hδ1 g))) (mul_self_nonneg _)

def scaledMatrix (K : Matrix I I ℝ) (α : I → ℝ) : Matrix I I ℝ :=
  fun i j => α i * K i j * α j

/-- Undo diagonal normalization and subtract the entries corresponding to
invalid repeated removals. Zero scale coordinates also restore zero rows. -/
def weightedCorrection (K : Matrix I I ℝ) (W : ℝ) (α κ : I → ℝ) : Matrix I I ℝ :=
  W • scaledMatrix K α - Matrix.diagonal κ

lemma scaledMatrix_form (K : Matrix I I ℝ) (α x y : I → ℝ) :
    (scaledMatrix K α).toBilin' x y =
      K.toBilin' (fun i => α i * x i) (fun i => α i * y i) := by
  rw [Matrix.toBilin'_apply, Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [scaledMatrix]
  ring

lemma diagonalMatrix_form (κ x y : I → ℝ) :
    (Matrix.diagonal κ).toBilin' x y = ∑ i, κ i * x i * y i := by
  rw [Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- The exact quadratic effect of scaling and invalid-diagonal removal. -/
theorem weightedCorrection_form (K : Matrix I I ℝ) (W : ℝ) (α κ x y : I → ℝ) :
    (weightedCorrection K W α κ).toBilin' x y =
      W * K.toBilin' (fun i => α i * x i) (fun i => α i * y i) -
        ∑ i, κ i * x i * y i := by
  simp only [weightedCorrection, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, scaledMatrix_form, diagonalMatrix_form]

/-- This includes the full unsummed two-removal signature: positive scalar
and diagonal congruence, invalid diagonals removed, zero rows restored. -/
theorem correctedTwoLevel_onePositive (line : I → G) (inner : I → Bool) (γ δ : G → ℝ)
    (W : ℝ) (α κ : I → ℝ)
    (hγ0 : ∀ g, 0 ≤ γ g) (hγ1 : ∀ g, γ g ≤ 1) (hδ1 : ∀ g, δ g ≤ 1)
    (hW : 0 ≤ W) (hκ : ∀ i, 0 ≤ κ i) :
    OnePositiveDirection (weightedCorrection (twoLevelKernel line inner γ δ) W α κ).toBilin' := by
  refine onePositiveDirection_of_kernel _ ?_ (vectorSum α) ?_
  · intro x y
    rw [weightedCorrection_form, weightedCorrection_form,
      twoLevelKernel_form_symm line inner γ δ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro v hv
    have hsum : vectorSum (fun _ : I => 1) (fun i => α i * v i) = 0 := by
      simpa only [vectorSum_apply, one_mul] using hv
    have hK := twoLevelKernel_nonpositive line inner γ δ hγ0 hγ1 hδ1
      (fun i => α i * v i) hsum
    have hnegative := mul_nonpos_of_nonneg_of_nonpos hW hK
    have hdiagonal : 0 ≤ ∑ i, κ i * v i * v i := by
      apply Finset.sum_nonneg
      intro i _
      have h := mul_nonneg (hκ i) (mul_self_nonneg (v i))
      nlinarith
    rw [weightedCorrection_form]
    linarith

end TwoLevel

end ContingencyTables

end OAI
