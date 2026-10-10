import OAI.Analysis.OperatorAlgebra.CyclicGNSUnitary
import OAI.Analysis.WeakInfiniteness.TensorFoundations
import OAI.Analysis.OperatorAlgebra.IsometricCornerOperators

namespace OAI

/-! Bundled GNS spaces keep the canonical Hilbert structures explicit when
specializing to concrete represented corners. -/
noncomputable section
open scoped ComplexOrder
namespace WeakPureInfiniteness

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The usual GNS Hilbert space, with its existing canonical structures. -/
def gnsHilbert (φ : A →ₚ[ℂ] ℂ) : ComplexHilbert where
  Carrier := φ.GNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The cyclic isometry with a bundled source Hilbert space. -/
def cyclicBundledGNSIsometry (φ : A →ₚ[ℂ] ℂ) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) (hφ : ∀ a, φ a = inner ℂ ξ (π a ξ)) :
    gnsHilbert φ →ₗᵢ[ℂ] H := cyclicGNSIsometry φ π ξ hφ

lemma cyclicBundledGNSIsometry_vector (φ : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hφ : ∀ a, φ a = inner ℂ ξ (π a ξ)) (a : A) :
    cyclicBundledGNSIsometry φ π ξ hφ (φ.toPreGNS a : φ.GNS) = π a ξ :=
  cyclicGNSIsometry_vector φ π ξ hφ a

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A normalized corner vector realizes the state on its GNS space. -/
def normalizedCornerGNSInclusion (V : K →ₗᵢ[ℂ] H) (φ : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (z : H)
    (hφ : ∀ a, φ a = inner ℂ
      (((‖z‖⁻¹ : ℝ) : ℂ) • V.toContinuousLinearMap.adjoint z)
      (π a (((‖z‖⁻¹ : ℝ) : ℂ) • V.toContinuousLinearMap.adjoint z))) :
    gnsHilbert φ →ₗᵢ[ℂ] H :=
  V.comp (cyclicBundledGNSIsometry φ π
    (((‖z‖⁻¹ : ℝ) : ℂ) • V.toContinuousLinearMap.adjoint z) hφ)

lemma normalizedCornerGNSInclusion_vector (V : K →ₗᵢ[ℂ] H) (φ : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (z : H)
    (hφ : ∀ a, φ a = inner ℂ
      (((‖z‖⁻¹ : ℝ) : ℂ) • V.toContinuousLinearMap.adjoint z)
      (π a (((‖z‖⁻¹ : ℝ) : ℂ) • V.toContinuousLinearMap.adjoint z))) (a : A) :
    normalizedCornerGNSInclusion V φ π z hφ (φ.toPreGNS a : φ.GNS) =
      ((‖z‖⁻¹ : ℝ) : ℂ) • isometricCornerLift V (π a) z := by
  change V (cyclicBundledGNSIsometry φ π _ hφ (φ.toPreGNS a : φ.GNS)) = _
  rw [cyclicBundledGNSIsometry_vector, map_smul, map_smul]
  rfl

end WeakPureInfiniteness

end

end OAI
