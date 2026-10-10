import Mathlib
import OAI.Analysis.Commutator.TracialDevelopment

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

lemma rightMul_mem_unitary (u : unitary A) :
    rightMul τ hτ (u : A) ∈ unitary (τ.GNS →L[ℂ] τ.GNS) := by
  rw [Unitary.mem_iff]
  constructor
  · change (rightMul τ hτ (u : A)).adjoint * rightMul τ hτ (u : A) = 1
    rw [← rightMul_star, ← rightMul_mul, Unitary.mul_star_self_of_mem u.property, rightMul_one]
  · change rightMul τ hτ (u : A) * (rightMul τ hτ (u : A)).adjoint = 1
    rw [← rightMul_star, ← rightMul_mul, Unitary.coe_star_mul_self, rightMul_one]

noncomputable def conjugation (u : unitary A) : τ.GNS →ₗᵢ[ℂ] τ.GNS where
  toLinearMap := ((τ.gnsStarAlgHom (u : A)).comp
    (rightMul τ hτ (star u : A))).toLinearMap
  norm_map' x := by
    change ‖τ.gnsStarAlgHom (u : A) (rightMul τ hτ (star u : A) x)‖ = ‖x‖
    rw [ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.map_mem _ u.property)]
    exact ContinuousLinearMap.norm_map_of_mem_unitary
      (rightMul_mem_unitary τ hτ (star u)) x

@[simp] lemma conjugation_coe (u : unitary A) (a : A) :
    conjugation τ hτ u (τ.toPreGNS a : τ.GNS) =
      (τ.toPreGNS ((u : A) * a * (star u : A)) : τ.GNS) := by
  change τ.gnsStarAlgHom (u : A) (rightMul τ hτ (star u : A)
    (τ.toPreGNS a : τ.GNS)) = _
  rw [rightMul_coe, PositiveLinearMap.ofPreGNS_toPreGNS, left_coe, mul_assoc]

@[simp] lemma conjugation_vacuum (u : unitary A) :
    conjugation τ hτ u (vacuum τ) = vacuum τ := by
  rw [vacuum, conjugation_coe, mul_one, Unitary.mul_star_self_of_mem u.property]

noncomputable def algebraVector : A →ₗ[ℂ] τ.GNS :=
  (Completion.toComplL : τ.PreGNS →L[ℂ] τ.GNS).toLinearMap.comp τ.toPreGNS.toLinearMap

@[simp] lemma algebraVector_apply (a : A) : algebraVector τ a = (τ.toPreGNS a : τ.GNS) := rfl

lemma inner_algebraVector (a b : A) :
    inner ℂ (algebraVector τ a) (algebraVector τ b) = τ (star a * b) := by
  simp only [algebraVector_apply, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS]

lemma inner_vacuum_algebraVector (a : A) :
    inner ℂ (vacuum τ) (algebraVector τ a) = τ a := by
  change inner ℂ (algebraVector τ 1) (algebraVector τ a) = _
  rw [inner_algebraVector, star_one, one_mul]

lemma algebraVector_dense : DenseRange (algebraVector τ) := by
  have h := dense_cyclic_orbit τ
  change DenseRange (fun a => (τ.toPreGNS a : τ.GNS))
  simpa only [left_vacuum] using h

end Kadison.TracialGNS
end

end OAI
