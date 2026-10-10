import OAI.GroupTheory.PolycyclicRecognition.Algebra.RankOneRepresentation

namespace OAI

/-! # The scalar character of a rank-one integral representation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem rankOne_action_coordinate (D : Rep ℤ G) (e : D.V ≃ₗ[ℤ] ℤ)
    (g : G) (x : D) : e (D.ρ g x) = e x * e (D.ρ g (e.symm 1)) := by
  simpa only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply] using
    integralEnd_apply (e.conj (D.ρ g)) (e x)

def rankOneCharacter (D : Rep ℤ G) (e : D.V ≃ₗ[ℤ] ℤ) : G →* ℤ where
  toFun g := e (D.ρ g (e.symm 1))
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, Module.End.mul_apply, rankOne_action_coordinate]
    exact mul_comm _ _

theorem rankOneCharacter_eq_of_iso (D E : Rep ℤ G)
    (eD : D.V ≃ₗ[ℤ] ℤ) (eE : E.V ≃ₗ[ℤ] ℤ) (i : D ≅ E) :
    rankOneCharacter D eD = rankOneCharacter E eE := by
  let b := eD.symm.trans ((Representation.equivOfIso i).toLinearEquiv.trans eE)
  have hb : b 1 ≠ 0 := by
    intro h
    have he : b 1 = b 0 := by rw [map_zero]; exact h
    exact one_ne_zero (b.injective he)
  ext g
  apply mul_right_cancel₀ hb
  rw [← show b ((rankOneCharacter D eD) g) = (rankOneCharacter D eD) g * b 1 from
    integralEnd_apply b.toLinearMap ((rankOneCharacter D eD) g)]
  change eE (i.hom.hom (eD.symm (eD (D.ρ g (eD.symm 1))))) =
    eE (E.ρ g (eE.symm 1)) * eE (i.hom.hom (eD.symm 1))
  rw [LinearEquiv.symm_apply_apply, Rep.hom_comm_apply, rankOne_action_coordinate]
  exact mul_comm _ _

def scalarCharacterRep (χ : G →* ℤ) : Rep ℤ G :=
  Rep.of ((algebraMap ℤ (Module.End ℤ ℤ)).toMonoidHom.comp χ)

def rankOneCharacterIso (D : Rep ℤ G) (e : D.V ≃ₗ[ℤ] ℤ) :
    D ≅ scalarCharacterRep (rankOneCharacter D e) :=
  Rep.mkIso (Representation.Equiv.mk e (by
    intro g
    ext x
    change e (D.ρ g x) = e (D.ρ g (e.symm 1)) * e x
    rw [rankOne_action_coordinate, mul_comm]))

end PolycyclicRecognition

end

end OAI
