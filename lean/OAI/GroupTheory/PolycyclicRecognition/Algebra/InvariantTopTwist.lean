import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalScalarTwist
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalOrientationExtension

namespace OAI

/-! # Making rank-one top homology invariant by a scalar twist

The twist is trivial on the normal subgroup. Its character is obtained from
actual conjugation on rationalized homology, so no orientation extension is
assumed for an intermediate subgroup of a lattice quotient.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem exists_invariantTopTwist (N : Subgroup G) [N.Normal] (A : Rep ℤ G) (d : ℕ)
    (x : groupHomology (Rep.res N.subtype A) d) (hx : x ≠ 0)
    (htor : ∀ (a : ℤ) (y : groupHomology (Rep.res N.subtype A) d),
      a • y = 0 → a = 0 ∨ y = 0)
    (hcomm : ∀ y z : groupHomology (Rep.res N.subtype A) d, y ≠ 0 → z ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • y = b • z) :
    ∃ η : G →* ℚ, (∀ a : N, η (a : G) = 1) ∧
      Nonempty ((groupHomology (Rep.res N.subtype (rationalScalarTwist A η)) d) ≃ₗ[ℤ] ℚ) ∧
      ∀ g, normalHomologyMap ℤ N (rationalScalarTwist A η) d g = 𝟙 _ := by
  classical
  let R := Rep.res N.subtype A
  let ρ := normalHomologyAddAction N A d
  obtain ⟨e⟩ := rational_rankOne_equiv htor hcomm x hx
  let c := rationalActionCharacter ρ e
  let η := inverseSourceRationalCharacter c
  have hη : ∀ a : N, η (a : G) = 1 := by
    intro a
    change c ((a : G)⁻¹) = 1
    apply rationalActionCharacter_of_zsmul ρ e _ (1 : ℤ)
    intro z
    change (normalHomologyMap ℤ N A d ((a⁻¹ : N) : G)).hom z = (1 : ℤ) • z
    rw [normalHomologyMap_subgroup]
    simp only [one_zsmul, ModuleCat.id_apply]
  have hc : ∀ g, η g * c g = 1 := by
    intro g
    change c g⁻¹ * c g = 1
    rw [← map_mul, inv_mul_cancel, map_one]
  refine ⟨η, hη, ?_, scalarTwistHomology_trivial N A η hη d e hc⟩
  let J := (groupHomology.functor ℤ N d).mapIso (rationalScalarTwistRestrictionIso N A η hη)
  let I := rationalTensorHomologyIso R d
  exact ⟨J.symm.toLinearEquiv.trans (I.toLinearEquiv.trans (e.restrictScalars ℤ))⟩

end PolycyclicRecognition

end

end OAI
