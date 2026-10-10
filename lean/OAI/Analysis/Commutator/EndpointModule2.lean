import Mathlib
import OAI.Analysis.Commutator.EndpointModule

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion

namespace Kadison

variable {I : Type*} [Fintype I] [DecidableEq I]

def normalizedTrace (A : Matrix I I ℂ) : ℂ :=
  (Fintype.card I : ℂ)⁻¹ * Matrix.trace A

namespace MatrixModule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable (ρ : Matrix I I ℂ →⋆ₐ[ℂ] (E →L[ℂ] E)) (Ω : E)
  (htrace : ∀ a, inner ℂ Ω (ρ a Ω) = normalizedTrace a)

include htrace in
lemma inner_vector (a b : Matrix I I ℂ) :
    inner ℂ (ρ a Ω) (ρ b Ω) = normalizedTrace (star a * b) := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ Ω (star (ρ a) (ρ b Ω)) = _
  rw [← map_star]
  change inner ℂ Ω ((ρ (star a) * ρ b) Ω) = _
  rw [← map_mul, htrace]

include htrace in
lemma norm_vector_single (i j : I) :
    ‖ρ (Matrix.single i j 1) Ω‖ = Real.sqrt (Fintype.card I : ℝ)⁻¹ := by
  have hs : ‖ρ (Matrix.single i j 1) Ω‖ ^ 2 = (Fintype.card I : ℝ)⁻¹ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_vector ρ Ω htrace]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single,
      star_one, Matrix.single_mul_single_same, normalizedTrace,
      Matrix.trace_single_eq_same, mul_one]
    change ((Fintype.card I : ℂ)⁻¹).re = _
    rw [Complex.inv_re]
    simp
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

lemma projection_symmetric (i : I) :
    ∀ x y : E, inner ℂ (ρ (Matrix.single i i 1) x) y =
      inner ℂ x (ρ (Matrix.single i i 1) y) := by
  intro x y
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ x (star (ρ (Matrix.single i i 1)) y) = _
  rw [← map_star]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]

lemma projection_fixes_single (i j : I) :
    ρ (Matrix.single i i 1) (ρ (Matrix.single i j 1) Ω) =
      ρ (Matrix.single i j 1) Ω := by
  change (ρ (Matrix.single i i 1) * ρ (Matrix.single i j 1)) Ω = _
  rw [← map_mul, Matrix.single_mul_single_same, one_mul]

variable {F G : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

include htrace in
lemma endpoint_unit_bound
    (Y : Completion (E ⊗[ℂ] F) →L[ℂ] Completion (E ⊗[ℂ] G))
    (hY : ∀ a, Y.comp (HilbertTensor.map (ρ a) (1 : F →L[ℂ] F)) =
      (HilbertTensor.map (ρ a) (1 : G →L[ℂ] G)).comp Y)
    (i j : I) (x : F) (z : G) :
    ‖inner ℂ ((ρ (Matrix.single i j 1) Ω ⊗ₜ[ℂ] z : E ⊗[ℂ] G) : Completion _)
      (Y ((Ω ⊗ₜ[ℂ] x : E ⊗[ℂ] F) : Completion _))‖ ≤
      ‖Y‖ * (Fintype.card I : ℝ)⁻¹ * ‖x‖ * ‖z‖ := by
  have h := HilbertTensor.endpoint_projection_bound Y (ρ (Matrix.single i i 1))
    (projection_symmetric ρ i) (hY _) Ω (ρ (Matrix.single i j 1) Ω)
    (projection_fixes_single ρ Ω i j) x z
  rw [norm_vector_single ρ Ω htrace, norm_vector_single ρ Ω htrace,
    mul_assoc ‖Y‖, ← sq, Real.sq_sqrt (inv_nonneg.mpr (Nat.cast_nonneg _))] at h
  exact h

end MatrixModule

end Kadison
end

end OAI
