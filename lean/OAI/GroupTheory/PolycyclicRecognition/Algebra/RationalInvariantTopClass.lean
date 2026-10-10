import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalOrientationConjugation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalOrientationExtension

namespace OAI

/-! # An ambient rational twist with invariant nonzero kernel top homology -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem rationalOrientation_topLine (N : Subgroup G) (R : Rep ℤ N)
    (eR : R.V ≃ₗ[ℤ] ℤ) (d : ℕ) (χ : G →* ℚ)
    (hχ : ∀ a : N, χ (a : G) = (rankOneCharacter R eR a : ℚ))
    (x : groupHomology R d) (hx : x ≠ 0)
    (htor : ∀ (a : ℤ) (y : groupHomology R d), a • y = 0 → a = 0 ∨ y = 0)
    (hcomm : ∀ y z : groupHomology R d, y ≠ 0 → z ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • y = b • z) :
    Nonempty (groupHomology (Rep.res N.subtype (rationalCharacterRep χ)) d ≃ₗ[ℤ] ℚ) := by
  classical
  obtain ⟨e⟩ := rational_rankOne_equiv htor hcomm x hx
  let J := (groupHomology.functor ℤ N d).mapIso (rationalizedOrientationIso N R eR χ hχ)
  let I := rationalTensorHomologyIso R d
  exact ⟨J.symm.toLinearEquiv.trans (I.toLinearEquiv.trans (e.restrictScalars ℤ))⟩

theorem exists_rationalInvariantTopClass (N : Subgroup G) [N.Normal]
    (R : Rep ℤ N) (eR : R.V ≃ₗ[ℤ] ℤ) (d : ℕ)
    (x : groupHomology R d) (hx : x ≠ 0)
    (htor : ∀ (a : ℤ) (y : groupHomology R d), a • y = 0 → a = 0 ∨ y = 0)
    (hcomm : ∀ y z : groupHomology R d, y ≠ 0 → z ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • y = b • z)
    (hdetect : ∀ A : Rep ℤ N, Nonempty (A.V ≃ₗ[ℤ] ℤ) →
      (∃ y : groupHomology A d, y ≠ 0) → Nonempty (R ≅ A)) :
    ∃ χ : G →* ℚ, (∀ g, χ g ≠ 0) ∧
      (∀ a : N, χ (a : G) = (rankOneCharacter R eR a : ℚ)) ∧
      (∃ y : groupHomology (Rep.res N.subtype (rationalCharacterRep χ)) d, y ≠ 0) ∧
      ∀ g, normalHomologyMap ℤ N (rationalCharacterRep χ) d g = 𝟙 _ := by
  classical
  let hinv := orientation_action_invariant N R eR d x hx hdetect
  let ρ := invariantConjugationHomologyAction N R hinv d
  obtain ⟨e⟩ := rational_rankOne_equiv htor hcomm x hx
  let c := rationalActionCharacter ρ e
  let χ := inverseSourceRationalCharacter c
  have hχ : ∀ a : N, χ (a : G) = (rankOneCharacter R eR a : ℚ) := by
    intro a
    change c ((a : G)⁻¹) = _
    have hρ : ∀ z, ρ ((a : G)⁻¹) z = rankOneCharacter R eR a • z := by
      intro z
      have h := orientationHomology_inner_action N R hinv eR d a⁻¹
      rw [inv_inv] at h
      change (invariantConjugationHomologyMap N R hinv d ((a : G)⁻¹)).hom z = _
      calc
        _ = (rankOneCharacter R eR a • 𝟙 (groupHomology R d)).hom z :=
          congrArg (fun f : groupHomology R d ⟶ groupHomology R d => f.hom z) h
        _ = rankOneCharacter R eR a • z := rfl
    exact rationalActionCharacter_of_zsmul ρ e _ _ hρ
  have hc : ∀ g, χ g * c g = 1 := by
    intro g
    change c g⁻¹ * c g = 1
    rw [← map_mul, inv_mul_cancel, map_one]
  refine ⟨χ, fun g => rationalActionCharacter_ne_zero ρ e g⁻¹, hχ, ?_, ?_⟩
  · let I := rationalTensorHomologyIso R d
    let J := (groupHomology.functor ℤ N d).mapIso (rationalizedOrientationIso N R eR χ hχ)
    refine ⟨J.hom (I.inv (e.symm 1)), ?_⟩
    intro hz
    have hJ : Function.Injective J.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
    have hI : Function.Injective I.inv := (ModuleCat.mono_iff_injective _).mp inferInstance
    have hzero : e.symm 1 = 0 := hI (hJ (hz.trans (map_zero J.hom.hom).symm) |>.trans
      (map_zero I.inv.hom).symm)
    have h := congrArg e hzero
    exact one_ne_zero (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using h)
  · intro g
    exact rationalOrientationHomology_trivial N R eR χ hχ hinv d e hc g

end PolycyclicRecognition

end

end OAI
