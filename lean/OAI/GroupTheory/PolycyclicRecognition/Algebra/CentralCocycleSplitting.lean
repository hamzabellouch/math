import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnitaryQuotientCocycle

namespace OAI

/-! # Splitting a cocycle into central fixed and moving summands -/

noncomputable section

namespace PolycyclicRecognition

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E))

def centralFixedUnitary : G →* ((unitaryCentralFixed ρ) ≃ₗᵢ[ℝ] (unitaryCentralFixed ρ)) :=
  unitarySubspaceAction ρ (unitaryCentralFixed ρ) (fun g _ hx => unitaryCentralFixed_map ρ g hx)

def centralMovingUnitary : G →* ((unitaryCentralFixed ρ)ᗮ ≃ₗᵢ[ℝ] (unitaryCentralFixed ρ)ᗮ) :=
  unitarySubspaceAction ρ (unitaryCentralFixed ρ)ᗮ
    (fun g _ hx => unitaryCentralFixed_orthogonal_map ρ g hx)

theorem centralFixedUnitary_center (z : Subgroup.center G) : centralFixedUnitary ρ z = 1 := by
  ext x
  exact x.property z

theorem centralFixedUnitary_no_fixed
    (hfix : ∀ x : E, (∀ g, ρ g x = x) → x = 0)
    (v : unitaryCentralFixed ρ) (hv : ∀ g, centralFixedUnitary ρ g v = v) : v = 0 := by
  apply Subtype.ext
  apply hfix
  intro g
  exact congrArg Subtype.val (hv g)

theorem centralMovingUnitary_no_central_fixed
    (v : (unitaryCentralFixed ρ)ᗮ)
    (hv : ∀ z : Subgroup.center G, centralMovingUnitary ρ z v = v) : v = 0 := by
  apply unitaryCentralFixed_orthogonal_no_fixed ρ v
  intro z
  exact congrArg Subtype.val (hv z)

variable [CompleteSpace E]

def centralFixedProjection : E →L[ℝ] unitaryCentralFixed ρ :=
  (unitaryCentralFixed ρ).orthogonalProjectionOnto

def centralMovingProjection : E →L[ℝ] (unitaryCentralFixed ρ)ᗮ :=
  (unitaryCentralFixed ρ)ᗮ.orthogonalProjectionOnto

theorem centralFixedProjection_intertwines (g : G) (x : E) :
    centralFixedProjection ρ (ρ g x) = centralFixedUnitary ρ g (centralFixedProjection ρ x) :=
  unitarySubspace_projection_commutes ρ (unitaryCentralFixed ρ) _ g x

theorem centralMovingProjection_intertwines (g : G) (x : E) :
    centralMovingProjection ρ (ρ g x) = centralMovingUnitary ρ g (centralMovingProjection ρ x) :=
  unitarySubspace_projection_commutes ρ (unitaryCentralFixed ρ)ᗮ _ g x

theorem centralProjections_add (x : E) :
    (centralFixedProjection ρ x : E) + (centralMovingProjection ρ x : E) = x :=
  (unitaryCentralFixed ρ).starProjection_add_starProjection_orthogonal x

theorem centralFixedCocycle {b : G → E} (hb : IsUnitaryCocycle ρ b) :
    IsUnitaryCocycle (centralFixedUnitary ρ) (centralFixedProjection ρ ∘ b) :=
  hb.map (centralFixedProjection ρ) (centralFixedProjection_intertwines ρ)

theorem centralMovingCocycle {b : G → E} (hb : IsUnitaryCocycle ρ b) :
    IsUnitaryCocycle (centralMovingUnitary ρ) (centralMovingProjection ρ ∘ b) :=
  hb.map (centralMovingProjection ρ) (centralMovingProjection_intertwines ρ)

variable [TopologicalSpace G]

omit [CompleteSpace E] in
theorem centralFixedUnitary_continuous (hρ : ∀ x : E, Continuous (fun g : G => ρ g x))
    (v : unitaryCentralFixed ρ) : Continuous (fun g => centralFixedUnitary ρ g v) :=
  (hρ v).subtype_mk _

omit [CompleteSpace E] in
theorem centralMovingUnitary_continuous (hρ : ∀ x : E, Continuous (fun g : G => ρ g x))
    (v : (unitaryCentralFixed ρ)ᗮ) : Continuous (fun g => centralMovingUnitary ρ g v) :=
  (hρ v).subtype_mk _

end PolycyclicRecognition

end

end OAI
