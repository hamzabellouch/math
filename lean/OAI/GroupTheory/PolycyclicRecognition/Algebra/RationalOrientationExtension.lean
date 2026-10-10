import OAI.GroupTheory.PolycyclicRecognition.Algebra.OrientationInnerAction

namespace OAI

/-! # Extending the kernel orientation by its rational top homology

The conjugation action on the rationalized top homology gives an ambient
character. Inverting its source gives the original integral orientation on
the normal subgroup.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def inverseSourceRationalCharacter (χ : G →* ℚ) : G →* ℚ where
  toFun g := χ g⁻¹
  map_one' := by simp
  map_mul' g h := by rw [mul_inv_rev, map_mul, mul_comm]

theorem exists_rationalOrientationExtension (N : Subgroup G) [N.Normal]
    (R : Rep ℤ N) (eR : R.V ≃ₗ[ℤ] ℤ) (d : ℕ)
    (x : groupHomology R d) (hx : x ≠ 0)
    (htor : ∀ (a : ℤ) (y : groupHomology R d), a • y = 0 → a = 0 ∨ y = 0)
    (hcomm : ∀ y z : groupHomology R d, y ≠ 0 → z ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • y = b • z)
    (hdetect : ∀ A : Rep ℤ N, Nonempty (A.V ≃ₗ[ℤ] ℤ) →
      (∃ y : groupHomology A d, y ≠ 0) → Nonempty (R ≅ A)) :
    ∃ χ : G →* ℚ, (∀ g, χ g ≠ 0) ∧
      ∀ a : N, χ (a : G) = (rankOneCharacter R eR a : ℚ) := by
  let hinv := orientation_action_invariant N R eR d x hx hdetect
  let ρ := invariantConjugationHomologyAction N R hinv d
  obtain ⟨e⟩ := rational_rankOne_equiv htor hcomm x hx
  let c := rationalActionCharacter ρ e
  refine ⟨inverseSourceRationalCharacter c, ?_, ?_⟩
  · intro g
    exact rationalActionCharacter_ne_zero ρ e g⁻¹
  · intro a
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

end PolycyclicRecognition

end

end OAI
