import OAI.Analysis.MutuallyUnbiased.Completion.Complement

namespace OAI

/-! Rank-one frame identities used to calculate the complement projection. -/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

variable {I κ η n : Type*} [Fintype I] [Fintype κ] [Fintype η] [Fintype n]

/-- Sum of the rank-one operators of a finite vector family. -/
def frameOperator (v : κ → I → ℂ) : Matrix I I ℂ :=
  ∑ a, Matrix.vecMulVec (v a) (star (v a))

lemma frameOperator_idempotent [DecidableEq κ] (v : κ → I → ℂ)
    (hv : ∀ a b, star (v a) ⬝ᵥ v b = if a = b then 1 else 0) :
    frameOperator v * frameOperator v = frameOperator v := by
  classical
  simp only [frameOperator, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.vecMulVec_mul_vecMulVec, hv]
  simp [apply_ite]

lemma frameOperator_mul (v : κ → I → ℂ) (w : η → I → ℂ) (c : ℂ)
    (hvw : ∀ a b, star (v a) ⬝ᵥ w b = c) :
    frameOperator v * frameOperator w = c • Matrix.vecMulVec (∑ a, v a) (star (∑ b, w b)) := by
  classical
  simp only [frameOperator, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.vecMulVec_mul_vecMulVec, hvw, Matrix.vecMulVec_smul]
  ext i j
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Finset.sum_mul, Finset.mul_sum]

lemma frameOperator_mulVec (v : κ → n → ℂ) (w : n → ℂ) :
    frameOperator v *ᵥ w = ∑ a, (star (v a) ⬝ᵥ w) • v a := by
  simp [frameOperator, Matrix.sum_mulVec, Matrix.vecMulVec_mulVec]

lemma frameOperator_mulVec_of_inner (v : κ → n → ℂ) (w : n → ℂ) (c : ℂ)
    (h : ∀ a, star (v a) ⬝ᵥ w = c) :
    frameOperator v *ᵥ w = c • ∑ a, v a := by
  simp only [frameOperator_mulVec, h, Finset.smul_sum]

lemma frameOperator_mulVec_self [DecidableEq κ] (v : κ → n → ℂ)
    (h : ∀ a b, star (v a) ⬝ᵥ v b = if a = b then 1 else 0) (b : κ) :
    frameOperator v *ᵥ v b = v b := by
  rw [frameOperator_mulVec]
  simp [h]

/-- Transfer a Hermitian matrix across the complex dot product. -/
lemma dotProduct_mulVec_of_hermitian [DecidableEq n] (C : Matrix n n ℂ)
    (hC : Cᴴ = C) (u v : n → ℂ) :
    star u ⬝ᵥ (C *ᵥ v) = star (C *ᵥ u) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, hC]

lemma dotProduct_fixed_of_image [DecidableEq n] (C : Matrix n n ℂ)
    (hC : Cᴴ = C) (u v w : n → ℂ) (a : ℂ)
    (hu : C *ᵥ u = a • w) (hv : C *ᵥ v = v) :
    star u ⬝ᵥ v = star a * (star w ⬝ᵥ v) := by
  calc
    star u ⬝ᵥ v = star u ⬝ᵥ (C *ᵥ v) := by rw [hv]
    _ = star (C *ᵥ u) ⬝ᵥ v := dotProduct_mulVec_of_hermitian C hC u v
    _ = star a * (star w ⬝ᵥ v) := by
      rw [hu]
      simp [dotProduct, Finset.mul_sum, mul_assoc]

/-- Flatten the rank-one matrix associated with an arbitrary complex vector. -/
def projectorVector (v : n → ℂ) : n × n → ℂ := fun p => v p.1 * star (v p.2)

lemma projectorVector_inner (v w : n → ℂ) :
    star (projectorVector v) ⬝ᵥ projectorVector w =
      (star v ⬝ᵥ w) * star (star v ⬝ᵥ w) := by
  simp only [dotProduct, projectorVector, Pi.star_apply, star_sum, star_mul, star_star,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype n] in
lemma pinchingMatrix_eq_frameOperator [DecidableEq n] (v : κ → n → ℂ) :
    pinchingMatrix v = frameOperator (fun a => projectorVector (v a)) := by
  ext p q
  simp only [pinchingMatrix, frameOperator, Matrix.sum_apply, Matrix.vecMulVec_apply,
    projectorVector, Pi.star_apply, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro a _
  ring

end MUB6.Weiner

end OAI
