import OAI.NumberTheory.DukePrimeDegree.Arithmetic.CyclicFixedOrders

namespace OAI

/-!
# Propagating a zero to the normal closure

Cyclic factorization gives nonnegative upper bounds for the fixed-field
multiplicities. Cyclic induction then shows that a zero of any fixed
field forces a zero of the full extension. This avoids an assumption of
holomorphy for a general Artin quotient.
-/

noncomputable section
open scoped NumberField BigOperators Classical

namespace DukePrimeDegree

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [NumberField.IsTotallyReal E]
local instance zeroPropagationFintype : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _
local instance zeroPropagationSubgroupFinite (H : Subgroup (E ≃ₐ[F] E)) :
    NumberField.IsTotallyReal (IntermediateField.fixedField H) :=
  NumberField.IsTotallyReal.of_algebra _ E

omit [FiniteDimensional F E] in
theorem fixedFieldMultiplicity_nonneg
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (H : Subgroup (E ≃ₐ[F] E)) :
    0 ≤ fixedFieldMultiplicity β H :=
  zetaMultiplicity_nonneg _ hβ0 hβ1

theorem fixedFieldMultiplicity_eq_zero_of_cyclic
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hcyclic : ∀ C : Subgroup (E ≃ₐ[F] E), IsCyclic C → fixedFieldMultiplicity β C = 0)
    (H : Subgroup (E ≃ₐ[F] E)) : fixedFieldMultiplicity β H = 0 := by
  obtain ⟨b, hb⟩ := exists_cyclic_permutation_character_identity_inside H
  have h := fixedFieldMultiplicity_cyclic_relation H b hb hβ0 hβ1
  have hc (C : CyclicSubgroups H) : fixedFieldMultiplicity β (C.val.map H.subtype) = 0 := by
    apply hcyclic
    exact (C.val.equivMapOfInjective H.subtype H.subtype_injective).isCyclic.mp C.property
  simp only [hc, mul_zero, Finset.sum_const_zero] at h
  have hcard : (Fintype.card H : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := H)
  exact (mul_eq_zero.mp h.symm).resolve_left hcard

theorem extension_multiplicity_pos_of_fixedField_pos
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hcyclic : ∀ C : Subgroup (E ≃ₐ[F] E), IsCyclic C →
      fixedFieldMultiplicity β C ≤ zetaMultiplicity E β)
    (H : Subgroup (E ≃ₐ[F] E)) (hH : 0 < fixedFieldMultiplicity β H) :
    0 < zetaMultiplicity E β := by
  by_contra hn
  have hE : zetaMultiplicity E β = 0 :=
    le_antisymm (le_of_not_gt hn) (zetaMultiplicity_nonneg E hβ0 hβ1)
  have hzero := fixedFieldMultiplicity_eq_zero_of_cyclic hβ0 hβ1
    (fun C hC => le_antisymm (by simpa only [hE] using hcyclic C hC)
      (fixedFieldMultiplicity_nonneg hβ0 hβ1 C)) H
  exact (ne_of_gt hH) hzero

end DukePrimeDegree

end

end OAI
