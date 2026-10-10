import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalRepresentationFunctor

namespace OAI

/-! # The rational group dimension supplied by the integral rational coefficient -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

theorem rationalize_projectiveDimension_le (A : Rep.{0} ℤ G) (d : ℕ)
    (hd : HasProjectiveDimensionLE A d) :
    HasProjectiveDimensionLE (rationalizeRepresentation A) d := by
  let F := rationalizeRepresentationFunctor (G := G)
  induction d generalizing A with
  | zero =>
    have hp : Projective A := (projective_iff_hasProjectiveDimensionLE_zero A).mpr hd
    exact (projective_iff_hasProjectiveDimensionLE_zero _).mp (F.projective_obj_of_projective hp)
  | succ d ih =>
    let S := normalizedSyzygySequence A
    have hS := normalizedSyzygySequence_shortExact A
    have hk : HasProjectiveDimensionLE (normalizedSyzygy A) d :=
      hS.hasProjectiveDimensionLT_X₁ (d + 1)
        (hasProjectiveDimensionLT_of_ge (normalizedFreeRepresentation A) 1 (d + 1) (by omega)) hd
    have hki := ih (normalizedSyzygy A) hk
    let : Mono S.f := hS.mono_f
    let : Epi S.g := hS.epi_g
    let : Projective (F.obj (normalizedFreeRepresentation A)) :=
      F.projective_obj_of_projective (inferInstance : Projective (normalizedFreeRepresentation A))
    exact (hS.map F).hasProjectiveDimensionLT_X₃ (d + 1) hki
      (hasProjectiveDimensionLT_of_ge (F.obj (normalizedFreeRepresentation A)) 1 (d + 2) (by omega))

def rationalTrivialRetract :
    Retract (Rep.trivial ℚ G ℚ) (rationalizeRepresentation (Rep.trivial ℤ G ℚ)) := by
  let i : Rep.trivial ℚ G ℚ ⟶ rationalizeRepresentation (Rep.trivial ℤ G ℚ) :=
    Rep.ofHom ⟨(LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight ((1 : ℚ) ⊗ₜ[ℤ] (1 : ℚ)),
      fun g => by
        apply LinearMap.ext
        intro q
        change q • ((1 : ℚ) ⊗ₜ[ℤ] (1 : ℚ)) =
          ((rationalizeRepresentation (Rep.trivial ℤ G ℚ)).ρ g)
            (q • ((1 : ℚ) ⊗ₜ[ℤ] (1 : ℚ)))
        erw [map_smul]
        rfl⟩
  let r : rationalizeRepresentation (Rep.trivial ℤ G ℚ) ⟶ Rep.trivial ℚ G ℚ :=
    Rep.ofHom ⟨rationalLinearExtension (LinearMap.id : ℚ →ₗ[ℤ] ℚ), fun g => by
      apply TensorProduct.AlgebraTensorModule.ext
      intro q x
      rfl⟩
  refine ⟨i, r, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro q
  change rationalLinearExtension (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
    (q • ((1 : ℚ) ⊗ₜ[ℤ] (1 : ℚ))) = q
  rw [map_smul, rationalLinearExtension_tmul]
  simp

theorem rationalGroup_dimension_le_of_integral_rational (d : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℤ G ℚ) d) :
    HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d := by
  let := rationalize_projectiveDimension_le (Rep.trivial ℤ G ℚ) d hd
  exact (rationalTrivialRetract (G := G)).hasProjectiveDimensionLT (d + 1)

end PolycyclicRecognition

end

end OAI
