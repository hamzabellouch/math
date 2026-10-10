import OAI.Analysis.KadisonSimilarity.Representation.JointFiberRestriction
import OAI.Analysis.KadisonSimilarity.Representation.ConullRepresentationExtension

namespace OAI

/-! # Restriction and zero extension of range representations

The old-unit projection is unchanged by restriction along a unital map,
even when the represented map is nonunital. Restriction commutes with
zero extension from a conull base, so the canonical range identifications
are available at every base point, including the zero fibers.
-/

noncomputable section
namespace KadisonSimilarity

variable {B S F : Type*} [CStarAlgebra B] [CStarAlgebra S]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem nonunitalRestrict_projection (φ : B →⋆ₐ[ℂ] S)
    (τ : S →⋆ₙₐ[ℂ] (F →L[ℂ] F)) :
    nonunitalUnitProjection (τ.comp φ.toNonUnitalStarAlgHom) = nonunitalUnitProjection τ := by
  change τ (φ 1) = τ 1
  rw [map_one]

def nonunitalRestrictionFiberEquiv (φ : B →⋆ₐ[ℂ] S)
    (τ : S →⋆ₙₐ[ℂ] (F →L[ℂ] F)) :
    projectionFiber (nonunitalUnitProjection (τ.comp φ.toNonUnitalStarAlgHom))
        (nonunitalUnitProjection_isStarProjection (τ.comp φ.toNonUnitalStarAlgHom)) ≃ₗᵢ[ℂ]
      projectionFiber (nonunitalUnitProjection τ) (nonunitalUnitProjection_isStarProjection τ) :=
  projectionFiberEquivOfEq _ _ _ _ (nonunitalRestrict_projection φ τ)

@[simp] theorem nonunitalRestrictionFiberEquiv_coe (φ : B →⋆ₐ[ℂ] S)
    (τ : S →⋆ₙₐ[ℂ] (F →L[ℂ] F))
    (v : projectionFiber (nonunitalUnitProjection (τ.comp φ.toNonUnitalStarAlgHom))
      (nonunitalUnitProjection_isStarProjection (τ.comp φ.toNonUnitalStarAlgHom))) :
    (nonunitalRestrictionFiberEquiv φ τ v : F) = v := rfl

@[simp] theorem nonunitalRestrictionFiberEquiv_symm_coe (φ : B →⋆ₐ[ℂ] S)
    (τ : S →⋆ₙₐ[ℂ] (F →L[ℂ] F))
    (v : projectionFiber (nonunitalUnitProjection τ) (nonunitalUnitProjection_isStarProjection τ)) :
    ((nonunitalRestrictionFiberEquiv φ τ).symm v : F) = v := rfl

theorem nonunitalRestrictionFiberEquiv_intertwines (φ : B →⋆ₐ[ℂ] S)
    (τ : S →⋆ₙₐ[ℂ] (F →L[ℂ] F)) (b : B)
    (v : projectionFiber (nonunitalUnitProjection (τ.comp φ.toNonUnitalStarAlgHom))
      (nonunitalUnitProjection_isStarProjection (τ.comp φ.toNonUnitalStarAlgHom))) :
    nonunitalRestrictionFiberEquiv φ τ
        (nonunitalRangeRepresentation (τ.comp φ.toNonUnitalStarAlgHom) b v) =
      nonunitalRangeRepresentation τ (φ b) (nonunitalRestrictionFiberEquiv φ τ v) := by
  apply Subtype.ext
  simp only [nonunitalRestrictionFiberEquiv_coe, nonunitalRangeRepresentation_coe,
    NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom]

theorem nonunitalRestriction_range_conjugacy (φ : B →⋆ₐ[ℂ] S)
    (τ : S →⋆ₙₐ[ℂ] (F →L[ℂ] F)) :
    (nonunitalRestrictionFiberEquiv φ τ).conjStarAlgEquiv.toStarAlgHom.comp
        (nonunitalRangeRepresentation (τ.comp φ.toNonUnitalStarAlgHom)) =
      (nonunitalRangeRepresentation τ).comp φ := by
  apply StarAlgHom.ext
  intro b
  apply ContinuousLinearMap.ext
  intro v
  change nonunitalRestrictionFiberEquiv φ τ
    (nonunitalRangeRepresentation (τ.comp φ.toNonUnitalStarAlgHom) b
      ((nonunitalRestrictionFiberEquiv φ τ).symm v)) =
    nonunitalRangeRepresentation τ (φ b) v
  rw [nonunitalRestrictionFiberEquiv_intertwines, LinearIsometryEquiv.apply_symm_apply]

variable {Ω : Type*} (s : Set Ω)
    (φ : B →⋆ₐ[ℂ] S) (ρ : ∀ _x : s, Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F))

/-- Zero extension is functorial for restriction of the original algebra. -/
theorem zeroExtend_unitizationRestrict (x : Ω) :
    zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x =
      (zeroExtendNonunitalRepresentation s ρ x).comp φ.toNonUnitalStarAlgHom := by
  classical
  ext b
  simp only [NonUnitalStarAlgHom.comp_apply, zeroExtendNonunitalRepresentation_apply]
  by_cases hx : x ∈ s
  · simp only [zeroExtendOperatorField, dite_eq_left hx, unitizationRestrict_inr,
      StarAlgHom.coe_toNonUnitalStarAlgHom]
  · simp only [zeroExtendOperatorField, dite_eq_right hx]

theorem globalRestriction_projection (x : Ω) :
    nonunitalUnitProjection
        (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x) =
      nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x) := by
  rw [zeroExtend_unitizationRestrict, nonunitalRestrict_projection]

/-- The actual zero-extended fibers of the restricted and joint
representations are identified by the identity on ambient vectors. -/
def globalRestrictionFiberEquiv (x : Ω) :
    projectionFiber
        (nonunitalUnitProjection
          (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x))
        (nonunitalUnitProjection_isStarProjection
          (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x)) ≃ₗᵢ[ℂ]
      projectionFiber (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
        (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) :=
  projectionFiberEquivOfEq _ _ _ _ (globalRestriction_projection s φ ρ x)

@[simp] theorem globalRestrictionFiberEquiv_coe (x : Ω)
    (v : projectionFiber
      (nonunitalUnitProjection
        (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x))
      (nonunitalUnitProjection_isStarProjection
        (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x))) :
    (globalRestrictionFiberEquiv s φ ρ x v : F) = v := rfl

@[simp] theorem globalRestrictionFiberEquiv_symm_coe (x : Ω)
    (v : projectionFiber (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
      (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x))) :
    ((globalRestrictionFiberEquiv s φ ρ x).symm v : F) = v := rfl

theorem globalRestrictionFiberEquiv_intertwines (x : Ω) (b : B)
    (v : projectionFiber
      (nonunitalUnitProjection
        (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x))
      (nonunitalUnitProjection_isStarProjection
        (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x))) :
    globalRestrictionFiberEquiv s φ ρ x
        (nonunitalRangeRepresentation
          (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x) b v) =
      nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x) (φ b)
        (globalRestrictionFiberEquiv s φ ρ x v) := by
  apply Subtype.ext
  simp only [globalRestrictionFiberEquiv_coe, nonunitalRangeRepresentation_coe]
  exact congrArg (fun τ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F) => τ b (v : F))
    (zeroExtend_unitizationRestrict s φ ρ x)

/-- Exact equality of the global zero-extended range representations. -/
theorem globalRestriction_range_conjugacy (x : Ω) :
    (globalRestrictionFiberEquiv s φ ρ x).conjStarAlgEquiv.toStarAlgHom.comp
        (nonunitalRangeRepresentation
          (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x)) =
      (nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x)).comp φ := by
  apply StarAlgHom.ext
  intro b
  apply ContinuousLinearMap.ext
  intro v
  change globalRestrictionFiberEquiv s φ ρ x
    (nonunitalRangeRepresentation
      (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x) b
      ((globalRestrictionFiberEquiv s φ ρ x).symm v)) =
    nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x) (φ b) v
  rw [globalRestrictionFiberEquiv_intertwines, LinearIsometryEquiv.apply_symm_apply]

theorem globalRestriction_compression_conjugacy (x : Ω) (T : F →L[ℂ] F) :
    (globalRestrictionFiberEquiv s φ ρ x).conjStarAlgEquiv
        (projectionFiberCompression
          (nonunitalUnitProjection
            (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x))
          (nonunitalUnitProjection_isStarProjection
            (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x)) T) =
      projectionFiberCompression
        (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
        (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) T := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  change (globalRestrictionFiberEquiv s φ ρ x
    (projectionFiberCompression
      (nonunitalUnitProjection
        (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x))
      (nonunitalUnitProjection_isStarProjection
        (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x)) T
      ((globalRestrictionFiberEquiv s φ ρ x).symm v)) : F) = _
  simp only [globalRestrictionFiberEquiv_coe, projectionFiberCompression_coe,
    globalRestrictionFiberEquiv_symm_coe, globalRestriction_projection]

end KadisonSimilarity

end

end OAI
