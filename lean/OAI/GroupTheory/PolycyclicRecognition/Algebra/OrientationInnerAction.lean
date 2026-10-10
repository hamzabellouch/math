import OAI.GroupTheory.PolycyclicRecognition.Finiteness.OrientationHomologyAction
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InnerHomologyAction
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyCoefficientLinearity

namespace OAI

/-! # The restriction of the orientation-homology action to the kernel -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem rankOne_action_zsmul (R : Rep ℤ G) (eR : R.V ≃ₗ[ℤ] ℤ) (g : G) (v : R) :
    R.ρ g v = rankOneCharacter R eR g • v := by
  apply eR.injective
  rw [rankOne_action_coordinate, map_zsmul]
  exact mul_comm _ _

variable (N : Subgroup G) [N.Normal] (R : Rep ℤ N)
  (hinv : ∀ (g : G) (a : N), R.ρ (MulAut.conjNormal g a) = R.ρ a)

theorem orientationHomology_inner_relation (eR : R.V ≃ₗ[ℤ] ℤ) (d : ℕ) (a : N) :
    rankOneCharacter R eR a • invariantConjugationHomologyMap N R hinv d (a : G) =
      𝟙 (groupHomology R d) := by
  rw [invariantConjugationHomologyMap, ← homologyMap_coefficient_zsmul]
  have h := groupHomology.map_congr
    (A := R) (B := R)
    (f := (MulAut.conjNormal (H := N) (a : G)).toMonoidHom)
    (g := (MulAut.conj a).toMonoidHom)
    (φ := rankOneCharacter R eR a • invariantConjugationCoefficient N R hinv (a : G))
    (ψ := innerHomologyCoefficient R a) (by ext n; rfl) (by
      apply DFunLike.ext
      intro v
      exact (rankOne_action_zsmul R eR a v).symm) d
  exact h.trans (innerHomologyMap_eq_id R a d)

theorem orientationHomology_inner_action (eR : R.V ≃ₗ[ℤ] ℤ) (d : ℕ) (a : N) :
    invariantConjugationHomologyMap N R hinv d (a : G) =
      rankOneCharacter R eR a⁻¹ • 𝟙 (groupHomology R d) := by
  have hmul : rankOneCharacter R eR a⁻¹ * rankOneCharacter R eR a = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  calc
    _ = (rankOneCharacter R eR a⁻¹ * rankOneCharacter R eR a) •
        invariantConjugationHomologyMap N R hinv d (a : G) := by rw [hmul, one_zsmul]
    _ = rankOneCharacter R eR a⁻¹ •
        (rankOneCharacter R eR a • invariantConjugationHomologyMap N R hinv d (a : G)) :=
      mul_zsmul _ _ _
    _ = _ := by rw [orientationHomology_inner_relation N R hinv eR d a]

end PolycyclicRecognition

end

end OAI
