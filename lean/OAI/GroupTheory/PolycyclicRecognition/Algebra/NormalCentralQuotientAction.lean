import OAI.GroupTheory.PolycyclicRecognition.Algebra.CharacteristicCentralTransgression
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InnerHomologyAction

namespace OAI

/-! # Quotient actions on a normal subgroup's central extension

Inner automorphisms act trivially on second homology, and the central kernel
is fixed by the normal subgroup. Thus both actions descend to the actual
ambient quotient, as does the transgression intertwiner.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped IsMulCommutative
attribute [local instance 2000] Rep.hV2 Rep.instLinear

theorem integralSecondHomologyMap_conj {H : Type} [Group H] (h : H) :
    integralSecondHomologyMap (MulAut.conj h).toMonoidHom = LinearMap.id := by
  have he : groupHomology.map (MulAut.conj h).toMonoidHom
      (groupIntegralTrivialCoefficientMap (MulAut.conj h).toMonoidHom) 2 = 𝟙 _ := by
    have hc := innerHomologyMap_eq_id (integralTrivialCoefficient H) h 2
    refine (groupHomology.map_congr rfl ?_ 2).trans hc
    rfl
  exact congrArg ModuleCat.Hom.hom he

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]
  (C : Subgroup N) [C.Characteristic] [IsMulCommutative C]

def normalCentralHomologyRepresentation :
    Representation ℤ G (groupHomology.H2 (integralTrivialCoefficient (N ⧸ C))) :=
  automorphismSecondHomologyRepresentation
    ((characteristicQuotientAut C).comp (MulAut.conjNormal (H := N)))

def normalCentralKernelRepresentation : Representation ℤ G (Additive C) :=
  automorphismAdditiveRepresentation
    ((MulAut.characteristic C).comp (MulAut.conjNormal (H := N)))

omit [IsMulCommutative C] in
theorem normalCentralHomologyRepresentation_subgroup (n : N) :
    normalCentralHomologyRepresentation N C (n : G) = 1 := by
  have he : characteristicQuotientAut C (MulAut.conjNormal (H := N) (n : G)) =
      MulAut.conj ((QuotientGroup.mk' C) n) := by
    apply MulEquiv.ext
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective C q
    change (QuotientGroup.mk' C) (MulAut.conjNormal (H := N) (n : G) m) = _
    have hn : MulAut.conjNormal (H := N) (n : G) m = n * m * n⁻¹ := Subtype.ext rfl
    rw [hn, map_mul, map_mul, map_inv]
    rfl
  change integralSecondHomologyMap
    (characteristicQuotientAut C (MulAut.conjNormal (H := N) (n : G))).toMonoidHom = _
  rw [he, integralSecondHomologyMap_conj]
  rfl

theorem normalCentralKernelRepresentation_subgroup (hc : C ≤ Subgroup.center N) (n : N) :
    normalCentralKernelRepresentation N C (n : G) = 1 := by
  apply LinearMap.ext
  intro c
  apply Additive.toMul.injective
  apply Subtype.ext
  change n * c.toMul.val * n⁻¹ = c.toMul.val
  have hh : Commute n c.toMul.val := Subgroup.mem_center_iff.mp (hc c.toMul.property) n
  rw [hh.eq, mul_inv_cancel_right]

def normalCentralQuotientHomologyAction : Rep ℤ (G ⧸ N) :=
  Rep.of (QuotientGroup.lift N (normalCentralHomologyRepresentation N C) (by
    intro g hg
    exact normalCentralHomologyRepresentation_subgroup N C ⟨g, hg⟩))

def normalCentralQuotientKernelAction (hc : C ≤ Subgroup.center N) : Rep ℤ (G ⧸ N) :=
  Rep.of (QuotientGroup.lift N (normalCentralKernelRepresentation N C) (by
    intro g hg
    exact normalCentralKernelRepresentation_subgroup N C hc ⟨g, hg⟩))

def normalCentralQuotientTransgression (hc : C ≤ Subgroup.center N) :
    normalCentralQuotientHomologyAction N C ⟶ normalCentralQuotientKernelAction N C hc :=
  Rep.ofHom {
    toLinearMap := characteristicCentralTransgression C hc
    isIntertwining' := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
      exact (characteristicCentralTransgressionIntertwining C hc
        (MulAut.conjNormal (H := N))).isIntertwining' g }

end PolycyclicRecognition

end

end OAI
