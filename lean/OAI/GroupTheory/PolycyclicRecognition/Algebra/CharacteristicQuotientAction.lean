import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalConjugation

namespace OAI

/-! # Automorphisms on a characteristic quotient -/

namespace PolycyclicRecognition

variable {G : Type} [Group G] (H : Subgroup G) [H.Characteristic]

def characteristicQuotientMap (e : MulAut G) : (G ⧸ H) →* G ⧸ H :=
  QuotientGroup.map H H e.toMonoidHom
    (Subgroup.characteristic_iff_le_comap.mp inferInstance e)

def characteristicQuotientAut : MulAut G →* MulAut (G ⧸ H) where
  toFun e :=
    { toFun := characteristicQuotientMap H e
      invFun := characteristicQuotientMap H e.symm
      left_inv := by
        intro x
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H x
        change (QuotientGroup.mk' H) (e.symm (e g)) = (QuotientGroup.mk' H) g
        rw [e.symm_apply_apply]
      right_inv := by
        intro x
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H x
        change (QuotientGroup.mk' H) (e (e.symm g)) = (QuotientGroup.mk' H) g
        rw [e.apply_symm_apply]
      map_mul' := (characteristicQuotientMap H e).map_mul }
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H x
    rfl
  map_mul' e f := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H x
    rfl

@[simp] theorem characteristicQuotientAut_mk (e : MulAut G) (g : G) :
    characteristicQuotientAut H e ((QuotientGroup.mk' H) g) =
      (QuotientGroup.mk' H) (e g) := rfl

end PolycyclicRecognition

end OAI
