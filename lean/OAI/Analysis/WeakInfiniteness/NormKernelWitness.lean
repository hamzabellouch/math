import Mathlib
import OAI.Analysis.WeakInfiniteness.DiagonalRegular
import OAI.Analysis.WeakInfiniteness.ReducedOperators
import OAI.Analysis.WeakInfiniteness.TensorIdealFunctional

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

lemma functional_norm_le_image {A B : Type*}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (q : A →⋆ₙₐ[ℂ] B) (φ : A →L[ℂ] ℂ)
    (hφ : ∀ y, q y = 0 → φ y = 0) (hφn : ‖φ‖ ≤ 1)
    (x : A) {M : ℝ} (hM : 0 < M) (hxn : ‖q x‖ ≤ M) : ‖φ x‖ ≤ M := by
  obtain ⟨z,hz,hzn⟩ := nonUnitalStarHom_exists_lift_norm_le q x hM hxn
  have hker : q (x-z) = 0 := by rw [map_sub,hz,sub_self]
  have hzero := hφ (x-z) hker
  have hval : φ x = φ z := sub_eq_zero.mp (by simpa only [map_sub] using hzero)
  rw [hval]
  exact (φ.le_opNorm z).trans
    ((mul_le_mul_of_nonneg_right hφn (norm_nonneg z)).trans
      (by simpa only [one_mul] using hzn))

lemma freeDiagonalFunctional_large_elementary_kernel (a b : FullGroupAlgebra (FreeGroup Bool))
    (hb : fullToReducedLarge b = 0) :
    freeDiagonalFunctional (minimalElementary a b) = 0 :=
  freeDiagonalFunctional_elementary_kernel a b (congrArg ULift.down hb)

lemma freeDiagonalFunctional_witness_gap :
    2 * Real.sqrt 3 < ‖freeDiagonalFunctional freeDiagonalWitness‖ := by
  rw [freeDiagonalFunctional_witness]
  norm_num
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]

lemma freeDiagonalFunctional_kernel_of_exact (hQ : Exact (FullGroupAlgebra (FreeGroup Bool)))
    (x : MinimalTensor (FullGroupAlgebra (FreeGroup Bool)) (FullGroupAlgebra (FreeGroup Bool)))
    (hx : minimalMapRight (A := FullGroupAlgebra (FreeGroup Bool)) (C := FullGroupAlgebra (FreeGroup Bool)) (D := ReducedFreeLarge) fullToReducedLarge.toNonUnitalStarAlgHom x = 0) :
    freeDiagonalFunctional x = 0 :=
  exact_functional_kernel (A := FullGroupAlgebra (FreeGroup Bool)) (B := FullGroupAlgebra (FreeGroup Bool)) (C := ReducedFreeLarge) hQ fullToReducedLarge.toNonUnitalStarAlgHom
    fullToReducedLarge_surjective freeDiagonalFunctional
    freeDiagonalFunctional_large_elementary_kernel x hx

lemma freeDiagonalFunctional_bound_of_kernel
    (hk : ∀ y : MinimalTensor (FullGroupAlgebra (FreeGroup Bool)) (FullGroupAlgebra (FreeGroup Bool)), minimalMapRight (A := FullGroupAlgebra (FreeGroup Bool)) (C := FullGroupAlgebra (FreeGroup Bool)) (D := ReducedFreeLarge) fullToReducedLarge.toNonUnitalStarAlgHom y = 0 →
      freeDiagonalFunctional y = 0) :
    ‖freeDiagonalFunctional freeDiagonalWitness‖ ≤ 2 * Real.sqrt 3 := by
  exact functional_norm_le_image (minimalMapRight (A := FullGroupAlgebra (FreeGroup Bool)) (C := FullGroupAlgebra (FreeGroup Bool)) (D := ReducedFreeLarge) fullToReducedLarge.toNonUnitalStarAlgHom)
    freeDiagonalFunctional hk norm_freeDiagonalFunctional_le freeDiagonalWitness
    (by positivity) norm_freeDiagonalWitness_reduced_le

theorem fullFreeTwo_not_exact : ¬ Exact (FullGroupAlgebra (FreeGroup Bool)) := by
  intro hQ
  exact not_le_of_gt freeDiagonalFunctional_witness_gap
    (freeDiagonalFunctional_bound_of_kernel (freeDiagonalFunctional_kernel_of_exact hQ))

end WeakPureInfiniteness
end

end OAI
