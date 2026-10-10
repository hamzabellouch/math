import OAI.Analysis.KadisonSimilarity.Derivation.TracialCornerCyclicity
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

namespace OAI

/-! The actual tracial GNS representation supplies the Hilbert geometry
used in the free-corner argument. Trace-preserving homomorphisms induce
isometric embeddings which intertwine the concrete left actions. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The canonical algebra vector in the completed GNS space. -/
def gnsTracialVector (τ : A →ₚ[ℂ] ℂ) : A →ₗ[ℂ] τ.GNS :=
  UniformSpace.Completion.toComplₗᵢ.toLinearMap.comp τ.toPreGNS.toLinearMap

@[simp] theorem gnsTracialVector_apply (τ : A →ₚ[ℂ] ℂ) (a : A) :
    gnsTracialVector τ a = (τ.toPreGNS a : τ.GNS) := rfl

theorem gnsTracialVector_inner (τ : A →ₚ[ℂ] ℂ) (a b : A) :
    inner ℂ (gnsTracialVector τ a) (gnsTracialVector τ b) = τ (star a * b) := by
  simp only [gnsTracialVector_apply, UniformSpace.Completion.inner_coe,
    PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.ofPreGNS_toPreGNS]

theorem gnsTracialVector_dense (τ : A →ₚ[ℂ] ℂ) : DenseRange (gnsTracialVector τ) :=
  UniformSpace.Completion.denseRange_coe.comp τ.toPreGNS.surjective.denseRange
    (UniformSpace.Completion.continuous_coe τ.PreGNS)

@[simp] theorem gnsTracialVector_left (τ : A →ₚ[ℂ] ℂ) (a b : A) :
    τ.gnsStarAlgHom a (gnsTracialVector τ b) = gnsTracialVector τ (a * b) := by
  change τ.gnsNonUnitalStarAlgHom a (τ.toPreGNS b : τ.GNS) =
    (τ.toPreGNS (a * b) : τ.GNS)
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
  rfl

/-- The concrete tracial geometry is obtained directly from the GNS
construction, rather than assumed as separate representation data. -/
def gnsTracialGeometry (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) : TracialCornerGeometry A τ.GNS where
  trace := τ.toLinearMap
  vector := gnsTracialVector τ
  left := τ.gnsStarAlgHom
  inner_vector := gnsTracialVector_inner τ
  tracial := htr
  dense_vector := gnsTracialVector_dense τ
  left_vector := gnsTracialVector_left τ

@[simp] theorem gnsTracialGeometry_trace (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) (a : A) :
    (gnsTracialGeometry τ htr).trace a = τ a := rfl

@[simp] theorem gnsTracialGeometry_vector (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) (a : A) :
    (gnsTracialGeometry τ htr).vector a = gnsTracialVector τ a := rfl

@[simp] theorem gnsTracialGeometry_left (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) (a : A) :
    (gnsTracialGeometry τ htr).left a = τ.gnsStarAlgHom a := rfl

theorem gnsTracialGeometry_trace_one (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1) :
    (gnsTracialGeometry τ htr).trace 1 = 1 := h1

theorem gnsTracialVector_injective (τ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, τ (star a * a) = 0 → a = 0) :
    Function.Injective (gnsTracialVector τ) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply hf
  rw [← gnsTracialVector_inner τ, map_sub, hab, sub_self, inner_zero_left]

section Hom

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ) (φ : A →⋆ₐ[ℂ] B)
  (hφ : ∀ a : A, τB (φ a) = τA a)

include hφ in
theorem gnsTracialHom_norm (a : A) :
    ‖gnsTracialVector τB (φ a)‖ = ‖gnsTracialVector τA a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    gnsTracialVector_inner, gnsTracialVector_inner, ← map_star φ, ← map_mul φ, hφ]

/-- The GNS isometry induced by a trace-preserving star homomorphism. -/
def gnsTracialHomIsometry : τA.GNS →ₗᵢ[ℂ] τB.GNS :=
  ((gnsTracialVector τB).comp φ.toAlgHom.toLinearMap).extendOfIsometry
    (gnsTracialVector_dense τA) (gnsTracialHom_norm τA τB φ hφ)

@[simp] theorem gnsTracialHomIsometry_vector (a : A) :
    gnsTracialHomIsometry τA τB φ hφ (gnsTracialVector τA a) =
      gnsTracialVector τB (φ a) :=
  LinearMap.extendOfIsometry_eq _ (gnsTracialVector_dense τA)
    (gnsTracialHom_norm τA τB φ hφ) a

/-- Intertwining holds on every completed GNS vector. -/
theorem gnsTracialHomIsometry_left (a : A) (ξ : τA.GNS) :
    gnsTracialHomIsometry τA τB φ hφ (τA.gnsStarAlgHom a ξ) =
      τB.gnsStarAlgHom (φ a) (gnsTracialHomIsometry τA τB φ hφ ξ) := by
  refine (gnsTracialVector_dense τA).induction_on ξ
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [gnsTracialVector_left, gnsTracialHomIsometry_vector, map_mul]

theorem gnsTracialHomIsometry_intertwines (a : A) :
    (gnsTracialHomIsometry τA τB φ hφ).toContinuousLinearMap.comp (τA.gnsStarAlgHom a) =
      (τB.gnsStarAlgHom (φ a)).comp
        (gnsTracialHomIsometry τA τB φ hφ).toContinuousLinearMap := by
  ext ξ
  exact gnsTracialHomIsometry_left τA τB φ hφ a ξ

end Hom

end KadisonSimilarity

end

end OAI
