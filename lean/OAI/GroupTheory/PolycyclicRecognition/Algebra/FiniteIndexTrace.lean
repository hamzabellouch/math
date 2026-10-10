import Mathlib.RepresentationTheory.FiniteIndex

namespace OAI

/-! # The index in the induction/coinduction trace -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex] (D : Rep.{0} ℤ G)

def finiteIndexLift : D ⟶ Rep.ind H.subtype (Rep.res H.subtype D) := by
  classical
  exact Rep.resCoindToHom H.subtype D (Rep.res H.subtype D) (𝟙 _) ≫
    (Rep.indCoindIso (Rep.res H.subtype D)).inv

def finiteIndexReturn : Rep.ind H.subtype (Rep.res H.subtype D) ⟶ D :=
  (Rep.indResHomEquiv H.subtype (Rep.res H.subtype D) D).symm (𝟙 _)

omit [H.FiniteIndex] in
@[simp] theorem finiteIndexReturn_mk (g : G) (a : D) :
    (finiteIndexReturn H D).hom
      (IndV.mk H.subtype (Rep.res H.subtype D).ρ g a) = D.ρ g⁻¹ a := by
  classical
  simp [finiteIndexReturn, Rep.indResHomEquiv]
  exact (Finsupp.sum_single_index (a := g) (b := (1 : ℤ))
    (h := fun i d => @SMul.smul ℤ D.V D.hV2.toSMul d (D.ρ i⁻¹ a))
    (D.hV2.zero_smul _)).trans (D.hV2.one_smul _)

theorem finiteIndexLift_return :
    finiteIndexLift H D ≫ finiteIndexReturn H D = H.index • (𝟙 D : D ⟶ D) := by
  classical
  let : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  ext a
  change (finiteIndexReturn H D).hom
      (Rep.coindToInd (Rep.res H.subtype D)
        ((Rep.resCoindToHom H.subtype D (Rep.res H.subtype D) (𝟙 _)).hom a)) =
    H.index • a
  rw [Rep.coindToInd_apply, map_sum]
  have hc : Fintype.card (Quotient (QuotientGroup.rightRel H)) = H.index := by
    rw [QuotientGroup.card_quotient_rightRel, ← Nat.card_eq_fintype_card, ← H.index_eq_card]
  rw [← hc, ← Finset.card_univ, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro c _
  induction c using Quotient.inductionOn with
  | h g =>
    simp only [Quotient.liftOn_mk, Rep.resCoindToHom_hom_apply_coe]
    change (finiteIndexReturn H D).hom
      (IndV.mk H.subtype (Rep.res H.subtype D).ρ g (D.ρ g a)) = a
    rw [finiteIndexReturn_mk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

end PolycyclicRecognition

end

end OAI
