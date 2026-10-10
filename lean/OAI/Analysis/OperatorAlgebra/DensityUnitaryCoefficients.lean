import OAI.Analysis.OperatorAlgebra.DensitySpatialRepresentation
import OAI.Analysis.Nuclearity.SpatialCoefficientEstimate

namespace OAI

/-! Pointwise unitary identities for the spatial Hilbert–Schmidt action. -/

noncomputable section
open scoped InnerProductSpace
namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma densityLeft_unitary_apply (U : H ≃ₗᵢ[ℂ] H)
    (z : NuclearUltrapower.HilbertSchmidt H) :
    densityLeftRepresentation (U : H →L[ℂ] H) z = hsLeftUnitary U z := by
  exact congrArg (fun V : NuclearUltrapower.HilbertSchmidt H →L[ℂ]
    NuclearUltrapower.HilbertSchmidt H => V z) (densityLeft_unitary U)

lemma densityRight_unitary_apply (U : H ≃ₗᵢ[ℂ] H)
    (z : NuclearUltrapower.HilbertSchmidt H) :
    densityRightRepresentation (MulOpposite.op (U : H →L[ℂ] H)) z = hsRightUnitary U z := by
  exact congrArg (fun V : NuclearUltrapower.HilbertSchmidt H →L[ℂ]
    NuclearUltrapower.HilbertSchmidt H => V z) (densityRight_unitary U)

lemma densityLeft_unitary_product_apply (T : H →L[ℂ] H) (U : H ≃ₗᵢ[ℂ] H)
    (z : NuclearUltrapower.HilbertSchmidt H) :
    (densityLeftRepresentation T * densityLeftRepresentation (U : H →L[ℂ] H)) z =
      densityLeftRepresentation (T * (U : H →L[ℂ] H)) z :=
  congrArg (fun V : NuclearUltrapower.HilbertSchmidt H →L[ℂ]
    NuclearUltrapower.HilbertSchmidt H => V z)
      (map_mul (densityLeftRepresentation (H := H)) T (U : H →L[ℂ] H)).symm

lemma density_unitary_defect_norm (U : H ≃ₗᵢ[ℂ] H)
    (z : NuclearUltrapower.HilbertSchmidt H) :
    ‖densityRightRepresentation (MulOpposite.op (U : H →L[ℂ] H)) z -
      densityLeftRepresentation (U : H →L[ℂ] H) z‖ =
      ‖hsLeftUnitary U z - hsRightUnitary U z‖ := by
  rw [densityRight_unitary_apply, densityLeft_unitary_apply, norm_sub_rev]

lemma density_unitary_product_coefficient (T : H →L[ℂ] H) (U : H ≃ₗᵢ[ℂ] H)
    (z : NuclearUltrapower.HilbertSchmidt H) :
    inner ℂ z ((densityLeftRepresentation T *
      densityLeftRepresentation (U : H →L[ℂ] H)) z) =
      inner ℂ z (densityLeftRepresentation (T * (U : H →L[ℂ] H)) z) :=
  congrArg (inner ℂ z) (densityLeft_unitary_product_apply T U z)

lemma density_unitary_product_error (T : H →L[ℂ] H) (U : H ≃ₗᵢ[ℂ] H)
    (z : NuclearUltrapower.HilbertSchmidt H) (hzn : ‖z‖ = 1) (α : ℂ) :
    ‖inner ℂ z ((densityLeftRepresentation T *
      densityRightRepresentation (MulOpposite.op (U : H →L[ℂ] H))) z) - α‖ ≤
      ‖densityLeftRepresentation T‖ * ‖hsLeftUnitary U z - hsRightUnitary U z‖ +
      ‖inner ℂ z (densityLeftRepresentation (T * (U : H →L[ℂ] H)) z) - α‖ := by
  have hb := norm_product_coefficient_error_le
    (H := NuclearUltrapower.HilbertSchmidt H) z hzn
    (densityLeftRepresentation (H := H) T)
    (densityRightRepresentation (H := H) (MulOpposite.op (U : H →L[ℂ] H)))
    (densityLeftRepresentation (H := H) (U : H →L[ℂ] H)) α
  exact hb.trans_eq (by rw [density_unitary_defect_norm, density_unitary_product_coefficient])

end WeakPureInfiniteness

end

end OAI
