import OAI.NumberTheory.DukePrimeDegree.Arithmetic.CyclicIntegerOrders
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.FixedFieldTower

namespace OAI

/-!
# Cyclic characters on the Galois group of a normal closure

The cyclic factorization over the fixed field of a subgroup gives a
character on that subgroup. The tower identification relates its values
to the original fixed-field zero multiplicities, as required for gluing.
-/

noncomputable section
open scoped NumberField Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

variable {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E]
variable [NumberField.IsTotallyReal E]
variable (C : Subgroup (E ≃ₐ[ℚ] E)) [IsCyclic C]
local instance : IsCyclic (E ≃ₐ[IntermediateField.fixedField C] E) :=
  (IntermediateField.subgroupEquivAlgEquiv C).isCyclic.mp inferInstance
local instance : NumberField.IsTotallyReal (IntermediateField.fixedField C) :=
  NumberField.IsTotallyReal.of_algebra _ E
local instance (L : IntermediateField (IntermediateField.fixedField C) E) :
    NumberField.IsTotallyReal L := NumberField.IsTotallyReal.of_algebra _ E

/-- The cyclic fixed field has no larger zero multiplicity than the
normal closure itself. -/
theorem fixedFieldMultiplicity_le_extension
    {N : ℕ} [NeZero N]
    (ψ : ((E ≃ₐ[IntermediateField.fixedField C] E) →* ℂˣ) →
      EvenRayCharacter (IntermediateField.fixedField C) N)
    (hid : ∀ χ, (ψ χ).idealHom = idealHom (IntermediateField.fixedField C) E χ)
    (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    (hD : (NumberField.discr E).natAbs ∣ N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    fixedFieldMultiplicity β C ≤ zetaMultiplicity E β :=
  zetaMultiplicity_le_of_cyclic_ray_family ψ hid hψ hD hβ0 hβ1

/-- A simple normal-closure zero gives the cyclic sign data directly in
terms of the original subgroup lattice. -/
theorem cyclic_fixedField_character
    {N : ℕ} [NeZero N]
    (ψ : ((E ≃ₐ[IntermediateField.fixedField C] E) →* ℂˣ) →
      EvenRayCharacter (IntermediateField.fixedField C) N)
    (hid : ∀ χ, (ψ χ).idealHom = idealHom (IntermediateField.fixedField C) E χ)
    (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    (hD : (NumberField.discr E).natAbs ∣ N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hsimple : zetaMultiplicity E β = 1) :
    ∃ χ : C →* ℝˣ,
      (∀ x : C, fixedFieldMultiplicity β (Subgroup.zpowers (x : E ≃ₐ[ℚ] E)) =
        if χ x = 1 then 1 else 0) ∧
      fixedFieldMultiplicity β C = if χ = 1 then 1 else 0 := by
  obtain ⟨χ, hχ⟩ := exists_real_character_of_simple_zeta ψ hid hψ hD hβ0 hβ1 hsimple
  let e := IntermediateField.subgroupEquivAlgEquiv C
  let χC : C →* ℝˣ := χ.comp e.toMonoidHom
  refine ⟨χC, ?_, ?_⟩
  · intro x
    let L := IntermediateField.extendScalars (IntermediateField.fixedField_le
      (show Subgroup.zpowers (x : E ≃ₐ[ℚ] E) ≤ C from Subgroup.zpowers_le.mpr x.property))
    have hx := hχ L
    rw [fixingSubgroup_extendScalars_zpowers, Subgroup.zpowers_le] at hx
    let D := IntermediateField.fixedField (Subgroup.zpowers (x : E ≃ₐ[ℚ] E))
    let eL : L ≃ₐ[ℚ] D :=
      { toFun := fun z => ⟨z.val, z.property⟩
        invFun := fun z => ⟨z.val, z.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl
        commutes' := fun _ => rfl }
    have hz := zetaMultiplicity_algEquiv eL hβ0 hβ1
    rw [hz] at hx
    by_cases hcx : χ (e x) = 1
    · simpa only [fixedFieldMultiplicity, MonoidHom.mem_ker, χC, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, e, D, hcx, ite_true] using hx
    · simpa only [fixedFieldMultiplicity, MonoidHom.mem_ker, χC, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, e, D, hcx, ite_false] using hx
  · have hcomp : χC = 1 ↔ χ = 1 := by
      constructor
      · intro h
        apply MonoidHom.ext
        intro g
        obtain ⟨x, rfl⟩ := e.surjective g
        exact DFunLike.congr_fun h x
      · rintro rfl
        rfl
    have hbot := hχ (⊥ : IntermediateField (IntermediateField.fixedField C) E)
    have hbase := zetaMultiplicity_algEquiv
      ((IntermediateField.botEquiv (IntermediateField.fixedField C) E).restrictScalars ℚ)
      hβ0 hβ1
    rw [hbase, IntermediateField.fixingSubgroup_bot, top_le_iff,
      MonoidHom.ker_eq_top_iff, ← hcomp] at hbot
    by_cases hprincipal : χC = 1
    · simpa only [fixedFieldMultiplicity, hprincipal, ite_true] using hbot
    · simpa only [fixedFieldMultiplicity, hprincipal, ite_false] using hbot

end DukePrimeDegree

end

end OAI
