import OAI.Analysis.BoundedHochschild.NormalOrbitHull
import OAI.Analysis.BoundedHochschild.FiniteTraceCover

namespace OAI

/-!
# Positive normal and singular parts

The normal-vector projection splits a positive functional into positive
normal and singular parts. In particular, any positive functional dominated
by a normal positive functional is normal. This supplies the normality
criterion for order intervals in the predual compactness argument.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u v

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

section Representation
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder M] [StarOrderedRing M] in
lemma normalPart_diagonal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    scalarNormalPart e (coefficient π ξ ξ) =
      coefficient π (normalProjection e π ξ) (normalProjection e π ξ) := by
  rw [scalarNormalPart_coefficient]
  ext a
  let P := normalProjection e π
  have hPP : P (P ξ) = P ξ :=
    Submodule.starProjection_eq_self_iff.mpr (by simp [P, normalProjection])
  have hcomm : P (π a (P ξ)) = π a (P (P ξ)) :=
    congrArg (fun T : H →L[ℂ] H => T (P ξ)) (normalProjection_mul e π a)
  change inner ℂ ξ (π a (P ξ)) = inner ℂ (P ξ) (π a (P ξ))
  calc
    _ = inner ℂ ξ (P (π a (P ξ))) := by rw [hcomm, hPP]
    _ = _ := ((normalVectors e π).inner_starProjection_left_eq_right ξ (π a (P ξ))).symm

omit [PartialOrder M] [StarOrderedRing M] in
lemma normalComplement_diagonal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    coefficient π ξ ξ - scalarNormalPart e (coefficient π ξ ξ) =
      coefficient π (ξ - normalProjection e π ξ) (ξ - normalProjection e π ξ) := by
  rw [scalarNormalPart_coefficient]
  ext a
  let P := normalProjection e π
  let δ := ξ - P ξ
  have hPP : P (P ξ) = P ξ :=
    Submodule.starProjection_eq_self_iff.mpr (by simp [P, normalProjection])
  have hPδ : P δ = 0 := by dsimp [δ]; rw [map_sub, hPP, sub_self]
  have hcomm : P (π a δ) = π a (P δ) :=
    congrArg (fun T : H →L[ℂ] H => T δ) (normalProjection_mul e π a)
  have hzero : inner ℂ (P ξ) (π a δ) = 0 := by
    calc
      _ = inner ℂ ξ (P (π a δ)) :=
        (normalVectors e π).inner_starProjection_left_eq_right ξ (π a δ)
      _ = 0 := by rw [hcomm, hPδ, map_zero, inner_zero_right]
  change inner ℂ ξ (π a ξ) - inner ℂ ξ (π a (P ξ)) = inner ℂ δ (π a δ)
  calc
    _ = inner ℂ ξ (π a δ) := by dsimp [δ]; rw [map_sub, inner_sub_right]
    _ = inner ℂ (P ξ + δ) (π a δ) := by simp only [δ, add_sub_cancel]
    _ = inner ℂ δ (π a δ) := by rw [inner_add_left, hzero, zero_add]

end Representation

/-- The positive normal part, realized by a projected GNS vector. -/
def positiveNormalPart (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (ψ : M →ₚ[ℂ] ℂ) :
    M →ₚ[ℂ] ℂ :=
  vectorPositiveFunctional ψ.gnsStarAlgHom
    (normalProjection e ψ.gnsStarAlgHom (positiveVector ψ))

/-- The remaining positive part, realized by the complementary GNS vector. -/
def positiveSingularPart (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (ψ : M →ₚ[ℂ] ℂ) :
    M →ₚ[ℂ] ℂ :=
  vectorPositiveFunctional ψ.gnsStarAlgHom
    (positiveVector ψ - normalProjection e ψ.gnsStarAlgHom (positiveVector ψ))

lemma positiveNormalPart_eq (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (ψ : M →ₚ[ℂ] ℂ) :
    positiveFunctionalCLM (positiveNormalPart e ψ) = scalarNormalPart e (positiveFunctionalCLM ψ) := by
  have hψ : positiveFunctionalCLM ψ = coefficient ψ.gnsStarAlgHom (positiveVector ψ)
      (positiveVector ψ) := by ext a; exact (positiveVector_coefficient ψ a).symm
  rw [hψ, normalPart_diagonal]
  rfl

lemma positiveSingularPart_eq (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (ψ : M →ₚ[ℂ] ℂ) :
    positiveFunctionalCLM (positiveSingularPart e ψ) =
      positiveFunctionalCLM ψ - scalarNormalPart e (positiveFunctionalCLM ψ) := by
  have hψ : positiveFunctionalCLM ψ = coefficient ψ.gnsStarAlgHom (positiveVector ψ)
      (positiveVector ψ) := by ext a; exact (positiveVector_coefficient ψ a).symm
  rw [hψ, normalComplement_diagonal]
  rfl

lemma positiveNormalPart_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (ψ : M →ₚ[ℂ] ℂ) :
    TraceInPredual e (positiveNormalPart e ψ) := by
  apply vectorPositiveFunctional_normal
  simp [normalProjection]

/-- Domination by a positive normal functional forces normality. -/
theorem positive_normal_of_dominated (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (χ ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (hle : ∀ a : M, 0 ≤ a → χ a ≤ ψ a) : TraceInPredual e χ := by
  let θ : M →ₚ[ℂ] ℂ :=
    { toLinearMap := ψ.toLinearMap - χ.toLinearMap
      monotone' := (monotone_iff_map_nonneg (ψ.toLinearMap - χ.toLinearMap)).mpr (fun a ha => sub_nonneg.mpr (hle a ha)) }
  have hsum : positiveFunctionalCLM χ + positiveFunctionalCLM θ = positiveFunctionalCLM ψ := by
    ext a
    change χ a + (ψ a - χ a) = ψ a
    abel
  have hψnormal : positiveFunctionalCLM ψ ∈ normalDual e := (mem_normalDual e _).mpr hψ
  have hS : positiveFunctionalCLM (positiveSingularPart e χ) +
      positiveFunctionalCLM (positiveSingularPart e θ) = 0 := by
    rw [positiveSingularPart_eq, positiveSingularPart_eq]
    calc
      _ = (positiveFunctionalCLM χ + positiveFunctionalCLM θ) -
          (scalarNormalPart e (positiveFunctionalCLM χ) +
            scalarNormalPart e (positiveFunctionalCLM θ)) := by abel
      _ = positiveFunctionalCLM ψ - scalarNormalPart e (positiveFunctionalCLM ψ) := by
        rw [← map_add, hsum]
      _ = 0 := by rw [scalarNormalPart_fixes e hψnormal, sub_self]
  have hzero : positiveFunctionalCLM (positiveSingularPart e χ) = 0 := by
    apply HochschildSakai.dual_zero_of_projection_zero e
    intro p hp
    have he := congrArg (fun F : StrongDual ℂ M => F p) hS
    change positiveSingularPart e χ p + positiveSingularPart e θ p = 0 at he
    apply le_antisymm _ ((positiveSingularPart e χ).map_nonneg hp.nonneg)
    calc
      positiveSingularPart e χ p ≤
          positiveSingularPart e χ p + positiveSingularPart e θ p :=
        le_add_of_nonneg_right ((positiveSingularPart e θ).map_nonneg hp.nonneg)
      _ = 0 := he
  rw [positiveSingularPart_eq] at hzero
  have hχnormal : positiveFunctionalCLM χ ∈ normalDual e := by
    rw [sub_eq_zero] at hzero
    rw [hzero]
    exact scalarNormalPart_mem e _
  exact (mem_normalDual e _).mp hχnormal

end KadisonRingrose
end BoundedHochschild

end

end OAI
