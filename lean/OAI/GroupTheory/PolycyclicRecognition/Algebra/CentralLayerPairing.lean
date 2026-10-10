import OAI.GroupTheory.PolycyclicRecognition.Algebra.ClassTwoCommutatorPairing
import Mathlib.LinearAlgebra.TensorProduct.Basic

namespace OAI

/-! # Bilinear commutators at an actual central-series step

If commutators with `N` are central, they factor through the abelianization
of the ambient group and any central quotient of `N`. This applies at the
last nonzero step of a lower central series.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement IsMulCommutative
variable {G : Type} [Group G] (N : Subgroup G)

def centralLayerCommutatorLeft (h : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G)
    (b : N) : G →* Subgroup.center G where
  toFun a := ⟨⁅a, (b : G)⁆, h (Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) b.property)⟩
  map_one' := Subtype.ext (commutatorElement_one_left _)
  map_mul' a c := Subtype.ext (commutator_mul_left_of_central a c b
    (h (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) b.property)))

def centralLayerCommutatorRight (h : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G)
    (a : Abelianization G) : N →* Subgroup.center G where
  toFun b := Abelianization.lift (centralLayerCommutatorLeft N h b) a
  map_one' := by
    induction a using QuotientGroup.induction_on with | H a =>
      exact Subtype.ext (commutatorElement_one_right a)
  map_mul' b c := by
    induction a using QuotientGroup.induction_on with | H a =>
      exact Subtype.ext (commutator_mul_right_of_central a b c
        (h (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) c.property)))

def centralLayerQuotientHom (h : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G)
    (K : Subgroup N) [K.Normal] (hK : K.map N.subtype ≤ Subgroup.center G)
    (a : Abelianization G) : (N ⧸ K) →* Subgroup.center G :=
  QuotientGroup.lift K (centralLayerCommutatorRight N h a) (by
    intro b hb
    induction a using QuotientGroup.induction_on with | H a =>
      apply Subtype.ext
      exact (show Commute a (b : G) from
        Subgroup.mem_center_iff.mp (hK ⟨b, hb, rfl⟩) a).commutator_eq)

def centralLayerPairing (h : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G)
    (K : Subgroup N) [K.Normal] [IsMulCommutative (N ⧸ K)]
    (hK : K.map N.subtype ≤ Subgroup.center G) :
    Additive (Abelianization G) →ₗ[ℤ]
      Additive (N ⧸ K) →ₗ[ℤ] Additive (Subgroup.center G) where
  toFun a := (centralLayerQuotientHom N h K hK a.toMul).toAdditive.toIntLinearMap
  map_add' a b := by
    apply LinearMap.ext
    intro c
    induction c using QuotientGroup.induction_on with | H c =>
      change Additive.ofMul (Abelianization.lift (centralLayerCommutatorLeft N h c)
        (a.toMul * b.toMul)) = _
      exact congrArg Additive.ofMul (map_mul
        (Abelianization.lift (centralLayerCommutatorLeft N h c)) a.toMul b.toMul)
  map_smul' n a := by
    apply LinearMap.ext
    intro c
    induction c using QuotientGroup.induction_on with | H c =>
      change Additive.ofMul (Abelianization.lift (centralLayerCommutatorLeft N h c)
        (a.toMul ^ n)) = _
      exact congrArg Additive.ofMul (map_zpow
        (Abelianization.lift (centralLayerCommutatorLeft N h c)) a.toMul n)

@[simp] theorem centralLayerPairing_value
    (h : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G)
    (K : Subgroup N) [K.Normal] [IsMulCommutative (N ⧸ K)]
    (hK : K.map N.subtype ≤ Subgroup.center G) (a : G) (b : N) :
    centralLayerPairing N h K hK (Additive.ofMul (Abelianization.of a))
      (Additive.ofMul ((QuotientGroup.mk' K) b)) =
      Additive.ofMul ⟨⁅a, (b : G)⁆, h (Subgroup.commutator_mem_commutator
        (Subgroup.mem_top _) b.property)⟩ := rfl

end PolycyclicRecognition

end

end OAI
