import OAI.Analysis.KadisonSimilarity.Representation.UnitizationProjection
import OAI.Analysis.KadisonSimilarity.Representation.CompressedBicommutant

namespace OAI

/-! # Bicommutant closure on the old-unit fibers

Restriction to the range of the old unit sends the represented unitization
bicommutant into the bicommutant of the genuine original-algebra
representation. This uses commutants and actual compression, including when
the range is the zero Hilbert space.
-/

noncomputable section
namespace KadisonSimilarity

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Retraction onto the closed range of an orthogonal projection is the
Hilbert adjoint of its inclusion. -/
theorem projectionFiberRetraction_eq_adjoint (p : K →L[ℂ] K) (hp : IsStarProjection p) :
    projectionFiberRetraction p hp =
      (projectionFiberInclusion p hp).toContinuousLinearMap.adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℂ (p x) (y : K) = inner ℂ x (y : K)
  have hadjoint : p.adjoint = p := hp.isSelfAdjoint.star_eq
  rw [← ContinuousLinearMap.adjoint_inner_right p x (y : K), hadjoint,
    projectionFiber_fixed]

/-- A supported operator is the zero extension of its actual compression. -/
theorem isometricExtension_projectionFiberCompression
    (p : K →L[ℂ] K) (hp : IsStarProjection p) (T : K →L[ℂ] K)
    (hleft : p * T = T) (hright : T * p = T) :
    isometricExtension (projectionFiberInclusion p hp)
      (projectionFiberCompression p hp T) = T := by
  rw [isometricExtension, ← projectionFiberRetraction_eq_adjoint,
    ContinuousLinearMap.comp_assoc]
  exact projectionFiberCompression_extension p hp T hleft hright

variable {B : Type*} [CStarAlgebra B]

theorem unitization_inr_left_support
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) (b : B) :
    unitizationProjection ρ * ρ (Unitization.inr b) = ρ (Unitization.inr b) := by
  change ρ (Unitization.inr (1 : B)) * ρ (Unitization.inr b) = _
  rw [← map_mul, ← Unitization.inr_mul, one_mul]

theorem unitization_inr_right_support
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) (b : B) :
    ρ (Unitization.inr b) * unitizationProjection ρ = ρ (Unitization.inr b) := by
  change ρ (Unitization.inr b) * ρ (Unitization.inr (1 : B)) = _
  rw [← map_mul, ← Unitization.inr_mul, mul_one]

theorem unitizationRangeRepresentation_eq_compression
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) (b : B) :
    unitizationRangeRepresentation ρ b =
      projectionFiberCompression (unitizationProjection ρ)
        (unitizationProjection_isStarProjection ρ) (ρ (Unitization.inr b)) :=
  projectionFiberAction_eq_compression _ _ _ (unitizationProjection_commutes ρ _)

/-- The zero extension of the original algebra's range representation is
the given represented inr element, not a new abstract representation. -/
theorem isometricExtension_unitizationRangeRepresentation
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) (b : B) :
    isometricExtension (projectionFiberInclusion (unitizationProjection ρ)
      (unitizationProjection_isStarProjection ρ)) (unitizationRangeRepresentation ρ b) =
      ρ (Unitization.inr b) := by
  rw [unitizationRangeRepresentation_eq_compression]
  exact isometricExtension_projectionFiberCompression _ _ _
    (unitization_inr_left_support ρ b) (unitization_inr_right_support ρ b)

/-- Every unitization element is its scalar part plus its inr part. -/
theorem unitization_representation_decomposition
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) (a : Unitization ℂ B) :
    ρ a = a.fst • (1 : K →L[ℂ] K) + ρ (Unitization.inr a.snd) := by
  calc
    ρ a = ρ (Unitization.inl a.fst + Unitization.inr a.snd) :=
      congrArg ρ (Unitization.inl_fst_add_inr_snd_eq a).symm
    _ = _ := by
      rw [map_add, ← Unitization.algebraMap_eq_inl]
      exact congrArg (fun T : K →L[ℂ] K => T + ρ (Unitization.inr a.snd))
        ((ρ.commutes a.fst).trans (Algebra.algebraMap_eq_smul_one a.fst))

/-- Operators in the commutant of the genuine old-unit range
representation extend to operators commuting with the full unitization. -/
theorem unitizationRange_commutant_extension_commutes
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (T : projectionFiber (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ)
      →L[ℂ] projectionFiber (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ))
    (hT : T ∈ (representationVonNeumannAlgebra (unitizationRangeRepresentation ρ)).commutant)
    (a : Unitization ℂ B) :
    isometricExtension (projectionFiberInclusion (unitizationProjection ρ)
      (unitizationProjection_isStarProjection ρ)) T * ρ a =
      ρ a * isometricExtension (projectionFiberInclusion (unitizationProjection ρ)
        (unitizationProjection_isStarProjection ρ)) T := by
  have hinr (b : B) :
      isometricExtension (projectionFiberInclusion (unitizationProjection ρ)
        (unitizationProjection_isStarProjection ρ)) T * ρ (Unitization.inr b) =
      ρ (Unitization.inr b) * isometricExtension
        (projectionFiberInclusion (unitizationProjection ρ)
          (unitizationProjection_isStarProjection ρ)) T := by
    have h := congrArg (isometricExtension (projectionFiberInclusion
      (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ)))
      (VonNeumannAlgebra.mem_commutant_iff.mp hT
        (unitizationRangeRepresentation ρ b)
        (mem_representationVonNeumannAlgebra (unitizationRangeRepresentation ρ) b)).symm
    simpa only [isometricExtension_mul,
      isometricExtension_unitizationRangeRepresentation] using h
  rw [unitization_representation_decomposition ρ a, mul_add, add_mul,
    mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hinr]

/-- Compression to the old-unit fiber preserves represented bicommutant
membership. No support condition on the original operator is required. -/
theorem unitizationFiberCompression_mem
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (Q : K →L[ℂ] K) (hQ : Q ∈ representationVonNeumannAlgebra ρ) :
    projectionFiberCompression (unitizationProjection ρ)
      (unitizationProjection_isStarProjection ρ) Q ∈
        representationVonNeumannAlgebra (unitizationRangeRepresentation ρ) := by
  rw [projectionFiberCompression, projectionFiberRetraction_eq_adjoint]
  exact compression_mem_of_extended_commutant
    (projectionFiberInclusion (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ))
    (representationVonNeumannAlgebra (unitizationRangeRepresentation ρ)) ρ
    (unitizationRange_commutant_extension_commutes ρ) Q hQ

end KadisonSimilarity

end

end OAI
