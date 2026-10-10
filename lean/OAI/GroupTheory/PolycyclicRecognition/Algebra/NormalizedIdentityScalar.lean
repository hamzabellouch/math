import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedIdentityClass

namespace OAI

/-! # A scalar annihilating an identity cocycle factors through a projective -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem normalizedIdentityClass_scalar_zero_stable (A : Rep.{0} ℤ G) (n : ℕ) (m : ℤ)
    (h : m • normalizedIdentityClass A (n + 1) = 0) :
    stableRepresentationClass ((iteratedNormalizedSyzygy (n + 1)).obj A)
      ((iteratedNormalizedSyzygy (n + 1)).obj A) (m • 𝟙 _) = 0 := by
  let C := (normalizedResolutionComplex A).linearYonedaObj ℤ
    ((iteratedNormalizedSyzygy (n + 1)).obj A)
  have hz : C.homologyπ (n + 1) (m • normalizedIdentityCycle A (n + 1)) = 0 := by
    rw [map_zsmul]
    exact h
  obtain ⟨r, hr⟩ := cochain_boundary_of_class_zero C n
    (m • normalizedIdentityCycle A (n + 1)) hz
  rw [map_zsmul, normalizedIdentityCycle_projection] at hr
  change (normalizedResolutionComplex A).d (n + 1) n ≫ r =
    m • normalizedResolutionProjection A (n + 1) at hr
  rw [normalizedResolutionComplex_d] at hr
  let r' : normalizedFreeRepresentation ((iteratedNormalizedSyzygy n).obj A) ⟶
      (iteratedNormalizedSyzygy (n + 1)).obj A := r
  let u : (iteratedNormalizedSyzygy (n + 1)).obj A ⟶
      normalizedFreeRepresentation ((iteratedNormalizedSyzygy n).obj A) :=
    kernel.ι (normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A))
  have hur : u ≫ r' = m • 𝟙 ((iteratedNormalizedSyzygy (n + 1)).obj A) := by
    apply (cancel_epi (normalizedFreeAugmentation ((iteratedNormalizedSyzygy (n + 1)).obj A))).mp
    change normalizedFreeStep ((iteratedNormalizedSyzygy n).obj A) ≫ r' =
      normalizedFreeAugmentation ((iteratedNormalizedSyzygy (n + 1)).obj A) ≫
        (m • 𝟙 ((iteratedNormalizedSyzygy (n + 1)).obj A))
    rw [Preadditive.comp_zsmul, Category.comp_id]
    exact hr
  exact (stableRepresentationClass_eq_zero_iff_projective_factor _).mpr
    ⟨normalizedFreeRepresentation ((iteratedNormalizedSyzygy n).obj A), inferInstance,
      u, r', hur⟩

end PolycyclicRecognition

end

end OAI
