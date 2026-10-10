import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralLayerPairing
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ScalarExteriorSurjection

namespace OAI

/-! # Tensor generators of a central commutator layer -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct commutatorElement IsMulCommutative
variable {G : Type} [Group G] (N : Subgroup G)
variable (h : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G)
  (K : Subgroup N) [K.Normal] [IsMulCommutative (N ⧸ K)]
  (hK : K.map N.subtype ≤ Subgroup.center G)

def centralLayerSubmodule : Submodule ℤ (Additive (Subgroup.center G)) :=
  (⁅(⊤ : Subgroup G), N⁆.subgroupOf (Subgroup.center G)).toAddSubgroup.toIntSubmodule

theorem centralLayerPairing_mem (a : Additive (Abelianization G)) (b : Additive (N ⧸ K)) :
    centralLayerPairing N h K hK a b ∈ centralLayerSubmodule N := by
  induction a using QuotientGroup.induction_on with | H a =>
    induction b using QuotientGroup.induction_on with | H b =>
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) b.property

def centralLayerTensor :
    (Additive (Abelianization G) ⊗[ℤ] Additive (N ⧸ K)) →ₗ[ℤ]
      Additive (Subgroup.center G) :=
  TensorProduct.lift (centralLayerPairing N h K hK)

theorem centralLayerTensor_mem (x : Additive (Abelianization G) ⊗[ℤ] Additive (N ⧸ K)) :
    centralLayerTensor N h K hK x ∈ centralLayerSubmodule N := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => exact centralLayerPairing_mem N h K hK a b
  | add x y hx hy =>
    simpa only [map_add] using (centralLayerSubmodule N).add_mem hx hy

def centralLayerTensorSurjection :
    (Additive (Abelianization G) ⊗[ℤ] Additive (N ⧸ K)) →ₗ[ℤ] centralLayerSubmodule N :=
  (centralLayerTensor N h K hK).codRestrict _ (centralLayerTensor_mem N h K hK)

theorem centralLayerTensor_range :
    LinearMap.range (centralLayerTensor N h K hK) = centralLayerSubmodule N := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact centralLayerTensor_mem N h K hK x
  · let U := (LinearMap.range (centralLayerTensor N h K hK)).toAddSubgroup.toSubgroup
    let P := U.map (Subgroup.center G).subtype
    have hP : ⁅(⊤ : Subgroup G), N⁆ ≤ P := by
      apply Subgroup.commutator_le.mpr
      intro a _ b hb
      let bN : N := ⟨b, hb⟩
      let z := centralLayerPairing N h K hK (Additive.ofMul (Abelianization.of a))
        (Additive.ofMul ((QuotientGroup.mk' K) bN))
      refine ⟨z.toMul, ?_, rfl⟩
      exact ⟨Additive.ofMul (Abelianization.of a) ⊗ₜ[ℤ]
        Additive.ofMul ((QuotientGroup.mk' K) bN), rfl⟩
    intro x hx
    obtain ⟨z, hz, he⟩ := hP hx
    have he' : z = x.toMul := Subtype.ext he
    change Additive.ofMul z ∈ LinearMap.range (centralLayerTensor N h K hK) at hz
    simpa only [he', ofMul_toMul] using hz

theorem centralLayerTensor_surjective :
    Function.Surjective (centralLayerTensorSurjection N h K hK) := by
  intro z
  obtain ⟨x, hx⟩ := (show (z : Additive (Subgroup.center G)) ∈
      LinearMap.range (centralLayerTensor N h K hK) by
    rw [centralLayerTensor_range N h K hK]
    exact z.property)
  exact ⟨x, Subtype.ext hx⟩

include h hK in
theorem centralLayer_scalar_finite (k : Type) [Field k]
    [Module.Finite k (k ⊗[ℤ] Additive (Abelianization G))]
    [Module.Finite k (k ⊗[ℤ] Additive (N ⧸ K))] :
    Module.Finite k (k ⊗[ℤ] centralLayerSubmodule N) := by
  let e := TensorProduct.AlgebraTensorModule.distribBaseChange ℤ k
    (Additive (Abelianization G)) (Additive (N ⧸ K))
  let : Module.Finite k (k ⊗[ℤ] (Additive (Abelianization G) ⊗[ℤ] Additive (N ⧸ K))) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  exact Module.Finite.of_surjective ((centralLayerTensorSurjection N h K hK).baseChange k)
    ((centralLayerTensorSurjection N h K hK).baseChange_surjective k
      (centralLayerTensor_surjective N h K hK))

def centralLayerAddEquiv [IsMulCommutative (⁅(⊤ : Subgroup G), N⁆ : Subgroup G)] :
    centralLayerSubmodule N ≃+ Additive (⁅(⊤ : Subgroup G), N⁆ : Subgroup G) where
  toFun z := Additive.ofMul ⟨z.val.toMul.val, z.property⟩
  invFun z := ⟨Additive.ofMul ⟨z.toMul.val, h z.toMul.property⟩, z.toMul.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

include h hK in
theorem central_commutator_scalar_finite (k : Type) [Field k]
    [IsMulCommutative (⁅(⊤ : Subgroup G), N⁆ : Subgroup G)]
    [Module.Finite k (k ⊗[ℤ] Additive (Abelianization G))]
    [Module.Finite k (k ⊗[ℤ] Additive (N ⧸ K))] :
    Module.Finite k (k ⊗[ℤ] Additive (⁅(⊤ : Subgroup G), N⁆ : Subgroup G)) := by
  let := centralLayer_scalar_finite N h K hK k
  let e := (centralLayerAddEquiv N h).toIntLinearEquiv.baseChange ℤ k _ _
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

end PolycyclicRecognition

end

end OAI
