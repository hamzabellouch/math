import OAI.GroupTheory.PolycyclicRecognition.Lattices.KernelCompletionHeight

namespace OAI

/-! # Extending an action to the nilpotent completion

Existence comes from the constructed homomorphism extension. Uniqueness on
the integer grid forces the extensions to satisfy the action law.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K G Q : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group G] [Group Q]
  {i : K →* G} (C : NilpotentKernelCompletion i) (ρ : Q →* MulAut G)
  (hρ : ∀ q, ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
    ((C.embed.comp (ρ q).toMonoidHom).comp i))

namespace NilpotentKernelCompletion

include hρ in
theorem action_extension_exists (q : Q) :
    ∃ A : MulAut C.carrier, ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞ A ∧
      ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞ A.symm ∧
      ∀ g, A (C.embed g) = C.embed (ρ q g) := by
  apply C.automorphism_extension (ρ q) (hρ q)
  have hi : (ρ q).symm = ρ q⁻¹ := (map_inv ρ q).symm
  rw [hi]
  exact hρ q⁻¹

def extendedAutomorphism (q : Q) : MulAut C.carrier :=
  (C.action_extension_exists ρ hρ q).choose

theorem extendedAutomorphism_smooth (q : Q) :
    ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞
      (C.extendedAutomorphism ρ hρ q) :=
  (C.action_extension_exists ρ hρ q).choose_spec.1

theorem extendedAutomorphism_embed (q : Q) (g : G) :
    C.extendedAutomorphism ρ hρ q (C.embed g) = C.embed (ρ q g) :=
  (C.action_extension_exists ρ hρ q).choose_spec.2.2 g

def extendedAction : Q →* MulAut C.carrier where
  toFun := C.extendedAutomorphism ρ hρ
  map_one' := by
    apply MulEquiv.toMonoidHom_injective
    apply C.hom_ext C.carrier _ _ (C.extendedAutomorphism_smooth ρ hρ 1) contMDiff_id
    intro g
    rw [MulEquiv.coe_toMonoidHom, C.extendedAutomorphism_embed]
    simp only [map_one, MulAut.one_apply]
    rfl
  map_mul' q r := by
    apply MulEquiv.toMonoidHom_injective
    apply C.hom_ext C.carrier
      (C.extendedAutomorphism ρ hρ (q * r)).toMonoidHom
      ((C.extendedAutomorphism ρ hρ q) * (C.extendedAutomorphism ρ hρ r)).toMonoidHom
      (C.extendedAutomorphism_smooth ρ hρ (q * r))
      ((C.extendedAutomorphism_smooth ρ hρ q).comp
        (C.extendedAutomorphism_smooth ρ hρ r))
    intro g
    change C.extendedAutomorphism ρ hρ (q * r) (C.embed g) =
      C.extendedAutomorphism ρ hρ q (C.extendedAutomorphism ρ hρ r (C.embed g))
    rw [C.extendedAutomorphism_embed, C.extendedAutomorphism_embed,
      C.extendedAutomorphism_embed, map_mul]
    rfl

@[simp] theorem extendedAction_embed (q : Q) (g : G) :
    C.extendedAction ρ hρ q (C.embed g) = C.embed (ρ q g) :=
  C.extendedAutomorphism_embed ρ hρ q g

theorem extendedAction_smooth (q : Q) :
    ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞ (C.extendedAction ρ hρ q) :=
  C.extendedAutomorphism_smooth ρ hρ q

theorem extendedAction_preserves_hom {M : Type} [RealNormedLieAlgebra M]
    [FiniteDimensional ℝ M] [PM : PolynomialExponentialCoordinates M]
    (π : C.carrier →* M) (hπ : ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, M)) ∞ π)
    (hinv : ∀ q g, π (C.embed (ρ q g)) = π (C.embed g)) (q : Q) (x : C.carrier) :
    π (C.extendedAction ρ hρ q x) = π x := by
  have he : π.comp (C.extendedAction ρ hρ q).toMonoidHom = π := by
    apply C.hom_ext M (π.comp (C.extendedAction ρ hρ q).toMonoidHom) π
      (hπ.comp (C.extendedAction_smooth ρ hρ q)) hπ
    intro g
    change π (C.extendedAction ρ hρ q (C.embed g)) = π (C.embed g)
    rw [extendedAction_embed]
    exact hinv q g
  exact DFunLike.congr_fun he x

end NilpotentKernelCompletion
end PolycyclicRecognition

end

end OAI
