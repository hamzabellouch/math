import OAI.Analysis.KadisonSimilarity.Representation.JointFiberCommutants
import OAI.Analysis.KadisonSimilarity.Representation.UnitizationProjection

namespace OAI

/-! # Restricting a joint unitized representation

A unital inclusion preserves the old-unit projection. Thus restricting
a joint unitized representation to one source preserves its actual Hilbert
range, and the range representations agree after the canonical identity
isometry between the two equal projection ranges.
-/

noncomputable section
namespace KadisonSimilarity

variable {B S F : Type*} [CStarAlgebra B] [CStarAlgebra S]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Restrict through the functorial map between the two unitizations. -/
def unitizationRestrict (φ : B →⋆ₐ[ℂ] S)
    (ρ : Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F)) :
    Unitization ℂ B →⋆ₐ[ℂ] (F →L[ℂ] F) :=
  ρ.comp (Unitization.starMap φ.toNonUnitalStarAlgHom)

@[simp] theorem unitizationRestrict_inr (φ : B →⋆ₐ[ℂ] S)
    (ρ : Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F)) (b : B) :
    unitizationRestrict φ ρ (Unitization.inr b) = ρ (Unitization.inr (φ b)) := by
  change ρ (Unitization.starMap φ.toNonUnitalStarAlgHom (Unitization.inr b)) = _
  rw [Unitization.starMap_inr]
  rfl

/-- Both old units act by exactly the same ambient projection. -/
theorem unitizationRestrict_projection (φ : B →⋆ₐ[ℂ] S)
    (ρ : Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F)) :
    unitizationProjection (unitizationRestrict φ ρ) = unitizationProjection ρ := by
  change unitizationRestrict φ ρ (Unitization.inr 1) = ρ (Unitization.inr 1)
  rw [unitizationRestrict_inr, map_one]

/-- Equal projections have the identity isometry between their ranges. -/
def projectionFiberEquivOfEq (p q : F →L[ℂ] F)
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p = q) :
    projectionFiber p hp ≃ₗᵢ[ℂ] projectionFiber q hq :=
  LinearIsometryEquiv.ofEq (projectionFiber p hp).toSubmodule
    (projectionFiber q hq).toSubmodule (by subst q; rfl)

@[simp] theorem projectionFiberEquivOfEq_coe (p q : F →L[ℂ] F)
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p = q)
    (v : projectionFiber p hp) :
    (projectionFiberEquivOfEq p q hp hq h v : F) = v := rfl

/-- Restriction preserves the range Hilbert space up to its canonical
identity-on-vectors isometry. -/
def unitizationRestrictionFiberEquiv (φ : B →⋆ₐ[ℂ] S)
    (ρ : Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F)) :
    projectionFiber (unitizationProjection (unitizationRestrict φ ρ))
        (unitizationProjection_isStarProjection (unitizationRestrict φ ρ)) ≃ₗᵢ[ℂ]
      projectionFiber (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ) :=
  projectionFiberEquivOfEq _ _ _ _ (unitizationRestrict_projection φ ρ)

@[simp] theorem unitizationRestrictionFiberEquiv_coe (φ : B →⋆ₐ[ℂ] S)
    (ρ : Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F))
    (v : projectionFiber (unitizationProjection (unitizationRestrict φ ρ))
      (unitizationProjection_isStarProjection (unitizationRestrict φ ρ))) :
    (unitizationRestrictionFiberEquiv φ ρ v : F) = v := rfl

@[simp] theorem unitizationRestrictionFiberEquiv_symm_coe (φ : B →⋆ₐ[ℂ] S)
    (ρ : Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F))
    (v : projectionFiber (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ)) :
    ((unitizationRestrictionFiberEquiv φ ρ).symm v : F) = v := rfl

/-- Compression of every ambient operator respects this identification,
not only operators from the represented source. -/
theorem unitizationRestriction_compression_conjugacy (φ : B →⋆ₐ[ℂ] S)
    (ρ : Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F)) (T : F →L[ℂ] F) :
    (unitizationRestrictionFiberEquiv φ ρ).conjStarAlgEquiv
        (projectionFiberCompression (unitizationProjection (unitizationRestrict φ ρ))
          (unitizationProjection_isStarProjection (unitizationRestrict φ ρ)) T) =
      projectionFiberCompression (unitizationProjection ρ)
        (unitizationProjection_isStarProjection ρ) T := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  change (unitizationRestrictionFiberEquiv φ ρ
    (projectionFiberCompression (unitizationProjection (unitizationRestrict φ ρ))
      (unitizationProjection_isStarProjection (unitizationRestrict φ ρ)) T
      ((unitizationRestrictionFiberEquiv φ ρ).symm v)) : F) = _
  simp only [unitizationRestrictionFiberEquiv_coe, projectionFiberCompression_coe,
    unitizationRestrictionFiberEquiv_symm_coe, unitizationRestrict_projection]

/-- The restricted range action is the joint action of the included
source element on the very same ambient vector. -/
theorem unitizationRestrictionFiberEquiv_intertwines (φ : B →⋆ₐ[ℂ] S)
    (ρ : Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F)) (b : B)
    (v : projectionFiber (unitizationProjection (unitizationRestrict φ ρ))
      (unitizationProjection_isStarProjection (unitizationRestrict φ ρ))) :
    unitizationRestrictionFiberEquiv φ ρ
        (unitizationRangeRepresentation (unitizationRestrict φ ρ) b v) =
      unitizationRangeRepresentation ρ (φ b) (unitizationRestrictionFiberEquiv φ ρ v) := by
  apply Subtype.ext
  simp only [unitizationRestrictionFiberEquiv_coe, unitizationRangeRepresentation_coe,
    unitizationRestrict_inr]

/-- Exact equality of the genuine representations after identifying the
two equal projection ranges. -/
theorem unitizationRestriction_range_conjugacy (φ : B →⋆ₐ[ℂ] S)
    (ρ : Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F)) :
    (unitizationRestrictionFiberEquiv φ ρ).conjStarAlgEquiv.toStarAlgHom.comp
        (unitizationRangeRepresentation (unitizationRestrict φ ρ)) =
      (unitizationRangeRepresentation ρ).comp φ := by
  apply StarAlgHom.ext
  intro b
  apply ContinuousLinearMap.ext
  intro v
  change unitizationRestrictionFiberEquiv φ ρ
    (unitizationRangeRepresentation (unitizationRestrict φ ρ) b
      ((unitizationRestrictionFiberEquiv φ ρ).symm v)) =
    unitizationRangeRepresentation ρ (φ b) v
  rw [unitizationRestrictionFiberEquiv_intertwines, LinearIsometryEquiv.apply_symm_apply]

end KadisonSimilarity

end

end OAI
