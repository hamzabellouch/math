import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteIndexOrientation

namespace OAI

/-! # Transport of a top-homology orientation along a group isomorphism -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G J : Type} [Group G] [Group J]

def restrictionHomLinearEquiv (e : G ≃* J) (D A : Rep ℤ J) :
    (D ⟶ A) ≃ₗ[ℤ] (Rep.res e.toMonoidHom D ⟶ Rep.res e.toMonoidHom A) where
  toFun := Rep.resMap e.toMonoidHom
  invFun f := Rep.ofHom ⟨f.hom.toLinearMap, by
    intro j
    simpa using f.hom.isIntertwining' (e.symm j)⟩
  left_inv f := by apply Rep.hom_ext; rfl
  right_inv f := by apply Rep.hom_ext; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def orientationRestrictionRoundtripIso (e : G ≃* J) (A : Rep ℤ G) :
    Rep.res e.toMonoidHom (Rep.res e.symm.toMonoidHom A) ≅ A :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℤ A.V) (by
    intro g
    ext a
    change A.ρ (e.symm (e g)) a = A.ρ g a
    rw [e.symm_apply_apply]))

theorem topHomology_orientation_of_equiv (e : G ≃* J) (n : ℕ) (D : Rep ℤ J)
    (hD : ∀ A : Rep ℤ J, Nonempty (groupHomology A n ≃ₗ[ℤ] (D ⟶ A))) :
    ∀ A : Rep ℤ G, Nonempty
      (groupHomology A n ≃ₗ[ℤ] (Rep.res e.toMonoidHom D ⟶ A)) := by
  intro A
  let B := Rep.res e.symm.toMonoidHom A
  let h := groupHomology.mapIso (A := A) (B := B) e (LinearEquiv.refl ℤ A.V) (by
    intro g
    ext a
    change A.ρ g a = A.ρ (e.symm (e g)) a
    rw [e.symm_apply_apply]) n
  obtain ⟨d⟩ := hD B
  exact ⟨h.toLinearEquiv.trans (d.trans ((restrictionHomLinearEquiv e D B).trans
    (Linear.homCongr ℤ (Iso.refl _) (orientationRestrictionRoundtripIso e A))))⟩

end PolycyclicRecognition

end

end OAI
