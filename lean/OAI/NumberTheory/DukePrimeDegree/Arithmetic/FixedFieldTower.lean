import OAI.NumberTheory.DukePrimeDegree.Arithmetic.SubfieldOrders

namespace OAI

/-!
# The cyclic fixed-field tower

The automorphisms over a fixed field are the original subgroup. Passing
to a smaller subgroup in this cyclic extension preserves the actual
underlying intermediate field, so the cyclic factorization applies to
the same fixed-field zeta orders used by descent.
-/

noncomputable section
open scoped Classical NumberField

namespace DukePrimeDegree

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

lemma subgroupEquivAlgEquiv_apply (C : Subgroup (E ≃ₐ[F] E)) (g : C) (x : E) :
    IntermediateField.subgroupEquivAlgEquiv C g x = (g : E ≃ₐ[F] E) x := rfl

lemma fixingSubgroup_extendScalars_fixedField
    (C D : Subgroup (E ≃ₐ[F] E)) (hDC : D ≤ C) :
    (IntermediateField.extendScalars (IntermediateField.fixedField_le hDC)).fixingSubgroup =
      (D.comap C.subtype).map (IntermediateField.subgroupEquivAlgEquiv C).toMonoidHom := by
  let e := IntermediateField.subgroupEquivAlgEquiv C
  apply SetLike.ext
  intro g
  rw [Subgroup.mem_map_equiv]
  change g ∈ (IntermediateField.extendScalars
    (IntermediateField.fixedField_le hDC)).fixingSubgroup ↔ (e.symm g : E ≃ₐ[F] E) ∈ D
  have hmem (σ : E ≃ₐ[F] E) : σ ∈ D ↔
      σ ∈ (IntermediateField.fixedField D).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_fixedField]
  rw [hmem]
  simp only [IntermediateField.mem_fixingSubgroup_iff,
    IntermediateField.mem_extendScalars]
  have he (x : E) : (e.symm g : E ≃ₐ[F] E) x = g x := by
    have h := congrArg (fun σ => σ x) (e.apply_symm_apply g)
    exact h
  simp only [he]

lemma zpowers_comap_subtype
    {G : Type*} [Group G] (C : Subgroup G) (x : C) :
    (Subgroup.zpowers (x : G)).comap C.subtype = Subgroup.zpowers x := by
  change (Subgroup.zpowers (C.subtype x)).comap C.subtype = _
  rw [← MonoidHom.map_zpowers C.subtype x,
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective]

lemma fixingSubgroup_extendScalars_zpowers
    (C : Subgroup (E ≃ₐ[F] E)) (x : C) :
    (IntermediateField.extendScalars (IntermediateField.fixedField_le
      (show Subgroup.zpowers (x : E ≃ₐ[F] E) ≤ C from
        Subgroup.zpowers_le.mpr x.property))).fixingSubgroup =
      Subgroup.zpowers (IntermediateField.subgroupEquivAlgEquiv C x) := by
  rw [fixingSubgroup_extendScalars_fixedField C (Subgroup.zpowers (x : E ≃ₐ[F] E))
    (Subgroup.zpowers_le.mpr x.property), zpowers_comap_subtype,
    MonoidHom.map_zpowers]
  rfl

end DukePrimeDegree

end

end OAI
