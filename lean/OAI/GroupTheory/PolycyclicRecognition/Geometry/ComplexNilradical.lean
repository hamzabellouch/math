import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexAdjointKernel

namespace OAI

/-! # The intrinsic meaning of the complex weight kernel

The common kernel consists exactly of the elements with nilpotent adjoint.
In particular it is preserved by every Lie automorphism. This identifies the
nilpotent factor without making a choice of triangular basis part of its data.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}

namespace ComplexTriangularAdjoint
variable (T : ComplexTriangularAdjoint L n)

theorem diagonal_mul (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

theorem diagonal_pow (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (k : ℕ) (i : Fin n) :
    (A ^ k) i i = (A i i) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, diagonal_mul _ _ (hA.pow k) hA, ih, pow_succ]

/-- Nilpotence of the real adjoint remains nilpotence after scalar extension. -/
theorem complex_ad_nilpotent (x : L) (hx : IsNilpotent (LieAlgebra.ad ℝ L x)) :
    IsNilpotent (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L) (complexificationLieHom L x)) := by
  obtain ⟨k, hk⟩ := hx
  let j := complexificationLieHom L
  let D := LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L) (j x)
  have intertwine (m : ℕ) (y : L) :
      (D ^ m) (j y) = j (((LieAlgebra.ad ℝ L x) ^ m) y) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ih]
      exact (j.map_lie x _).symm
  refine ⟨k, ?_⟩
  apply LinearMap.ext
  intro v
  induction v using TensorProduct.inductionOn with
  | tmul z y =>
    change (D ^ k) (z ⊗ₜ[ℝ] y) = 0
    have he : z ⊗ₜ[ℝ] y = z • j y := by
      change z ⊗ₜ[ℝ] y = z • ((1 : ℂ) ⊗ₜ[ℝ] y)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [he, map_smul, intertwine, hk]
    simp [j]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The nilpotent kernel is independent of the chosen complex triangular basis. -/
theorem mem_kernelIdeal_iff_ad_nilpotent (x : L) :
    x ∈ T.kernelIdeal ↔ IsNilpotent (LieAlgebra.ad ℝ L x) := by
  refine ⟨T.ad_nilpotent x, ?_⟩
  intro hx
  obtain ⟨k, hk⟩ := complex_ad_nilpotent x hx
  have hA : complexifiedAdjointMatrix L T.basis x ^ k = 0 := by
    change ((LinearMap.toMatrixAlgEquiv T.basis)
      (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L) ((1 : ℂ) ⊗ₜ[ℝ] x))) ^ k = 0
    change (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L) ((1 : ℂ) ⊗ₜ[ℝ] x)) ^ k = 0 at hk
    rw [← map_pow, hk, map_zero]
  ext i
  have hi := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i i) hA
  have hu : (complexifiedAdjointMatrix L T.basis x).IsUpperTriangular := T.upper _
  rw [diagonal_pow _ hu k i] at hi
  change complexifiedAdjointMatrix L T.basis x i i = 0
  exact eq_zero_of_pow_eq_zero (by simpa only [Matrix.zero_apply] using hi)

/-- Every Lie automorphism preserves this concrete nilpotent ideal. -/
theorem map_mem_kernelIdeal (f : L ≃ₗ⁅ℝ⁆ L) {x : L} (hx : x ∈ T.kernelIdeal) :
    f x ∈ T.kernelIdeal := by
  rw [T.mem_kernelIdeal_iff_ad_nilpotent] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  have intertwine (m : ℕ) (y : L) :
      ((LieAlgebra.ad ℝ L (f x)) ^ m) (f y) =
        f (((LieAlgebra.ad ℝ L x) ^ m) y) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ih]
      exact (f.map_lie x _).symm
  refine ⟨k, ?_⟩
  ext y
  obtain ⟨z, rfl⟩ := f.surjective y
  change ((LieAlgebra.ad ℝ L (f x)) ^ k) (f z) = 0
  rw [intertwine, hk]
  simp

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
