import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnitaryCentralFixed

namespace OAI

/-! # Restricting a unitary representation to an invariant closed summand -/

noncomputable section

namespace PolycyclicRecognition

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (K : Submodule ℝ E)
  (hK : ∀ (g : G) (x : E), x ∈ K → ρ g x ∈ K)

def unitarySubspaceEquiv (g : G) : K ≃ₗᵢ[ℝ] K where
  toFun x := ⟨ρ g x, hK g x x.property⟩
  invFun x := ⟨ρ g⁻¹ x, hK g⁻¹ x x.property⟩
  left_inv x := by
    apply Subtype.ext
    change ρ g⁻¹ (ρ g x) = x
    have he : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    exact congrArg (fun f : E ≃ₗᵢ[ℝ] E => f x) he
  right_inv x := by
    apply Subtype.ext
    change ρ g (ρ g⁻¹ x) = x
    have he : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun f : E ≃ₗᵢ[ℝ] E => f x) he
  map_add' x y := by apply Subtype.ext; exact map_add (ρ g) (x : E) (y : E)
  map_smul' c x := by apply Subtype.ext; exact map_smul (ρ g) c (x : E)
  norm_map' x := (ρ g).norm_map x

def unitarySubspaceAction : G →* (K ≃ₗᵢ[ℝ] K) where
  toFun := unitarySubspaceEquiv ρ K hK
  map_one' := by
    ext x
    change ρ 1 x = x
    rw [map_one]
    rfl
  map_mul' g h := by
    ext x
    change ρ (g * h) x = ρ g (ρ h x)
    rw [map_mul]
    rfl

theorem unitarySubspaceAction_apply (g : G) (x : K) :
    (unitarySubspaceAction ρ K hK g x : E) = ρ g x := rfl

include hK in
theorem unitarySubspace_map_eq (g : G) :
    K.map (ρ g).toLinearIsometry.toLinearMap = K := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hK g x hx
  · intro hy
    refine ⟨ρ g⁻¹ y, hK g⁻¹ y hy, ?_⟩
    change ρ g (ρ g⁻¹ y) = y
    have he : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun f : E ≃ₗᵢ[ℝ] E => f y) he

theorem unitarySubspace_projection_commutes [K.HasOrthogonalProjection] (g : G) (x : E) :
    K.orthogonalProjectionOnto (ρ g x) =
      unitarySubspaceAction ρ K hK g (K.orthogonalProjectionOnto x) := by
  have hm := unitarySubspace_map_eq ρ K hK g
  have : (K.map (ρ g).toLinearIsometry.toLinearMap).HasOrthogonalProjection :=
    hm.symm ▸ inferInstance
  have he := (ρ g).toLinearIsometry.map_starProjection K x
  have he' : ρ g (K.starProjection x) = K.starProjection (ρ g x) := by
    simpa only [hm, LinearIsometryEquiv.coe_toLinearIsometry] using he
  apply Subtype.ext
  exact he'.symm

end PolycyclicRecognition

end

end OAI
