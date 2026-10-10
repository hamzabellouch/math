import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ZetaCharacterRelations
import OAI.NumberTheory.DukePrimeDegree.Dynamics.SubgroupInduction

namespace OAI

/-!
# Integer zero orders of fixed fields

The actual continued Dedekind zeta functions have finite nonnegative
orders at real points between zero and one. Permutation character
identities therefore give ordinary integer relations on these orders.
-/

noncomputable section
open scoped NumberField BigOperators Classical

namespace DukePrimeDegree

/-- An integer-valued version of the continued zeta order. -/
def zetaMultiplicity (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (β : ℝ) : ℤ :=
  (zetaZeroOrder K β).untopD 0

theorem zetaZeroOrder_eq_multiplicity
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    zetaZeroOrder K β = (zetaMultiplicity K β : WithTop ℤ) := by
  obtain ⟨m, hm⟩ := zetaZeroOrder_finite_nonnegative (K := K) hβ0 hβ1
  change zetaZeroOrder K β = ((m : ℤ) : WithTop ℤ) at hm
  simp only [zetaMultiplicity, hm, WithTop.untopD_coe]

theorem zetaMultiplicity_nonneg
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 ≤ zetaMultiplicity K β := by
  obtain ⟨m, hm⟩ := zetaZeroOrder_finite_nonnegative (K := K) hβ0 hβ1
  change zetaZeroOrder K β = ((m : ℤ) : WithTop ℤ) at hm
  simp only [zetaMultiplicity, hm, WithTop.untopD_coe]
  exact_mod_cast Nat.zero_le m

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [NumberField.IsTotallyReal E]
local instance : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _
local instance (H : Subgroup (E ≃ₐ[F] E)) :
    NumberField.IsTotallyReal (IntermediateField.fixedField H) :=
  NumberField.IsTotallyReal.of_algebra _ E

def fixedFieldMultiplicity (β : ℝ) (H : Subgroup (E ≃ₐ[F] E)) : ℤ :=
  zetaMultiplicity (IntermediateField.fixedField H) β

theorem fixedFieldMultiplicity_conjugate
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (H : Subgroup (E ≃ₐ[F] E)) (a : E ≃ₐ[F] E) :
    fixedFieldMultiplicity β (H.map (MulAut.conj a).toMonoidHom) =
      fixedFieldMultiplicity β H := by
  unfold fixedFieldMultiplicity zetaMultiplicity
  rw [zetaZeroOrder_fixedField_conjugate H a hβ0 hβ1]

/-- An integer permutation-character relation gives the identical
relation on the orders of the corresponding fixed-field zeta functions. -/
theorem fixedFieldMultiplicity_relation
    {I : Type*} [Fintype I] (H : I → Subgroup (E ≃ₐ[F] E)) (c : I → ℤ)
    (hχ : ∀ g, (∑ i, (c i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
      ((E ≃ₐ[F] E) ⧸ H i)).character g) = 0)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∑ i, c i * fixedFieldMultiplicity β (H i)) = 0 := by
  apply integer_zeta_orders_of_characters (fun i => IntermediateField.fixedField (H i))
    c ?_ hβ0 hβ1 (fun i => fixedFieldMultiplicity β (H i))
    (fun i => zetaZeroOrder_eq_multiplicity _ hβ0 hβ1)
  intro g
  have hfix (i : I) : (IntermediateField.fixedField (H i)).fixingSubgroup = H i :=
    IntermediateField.fixingSubgroup_fixedField (H i)
  calc
    _ = ∑ i, (c i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ H i)).character g := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun S : Subgroup (E ≃ₐ[F] E) => (c i : ℂ) *
        (Representation.ofMulAction ℂ (E ≃ₐ[F] E) ((E ≃ₐ[F] E) ⧸ S)).character g) (hfix i)
    _ = 0 := hχ g

/-- Cyclic induction inside a subgroup controls the zero order of its
fixed field, including nonnormal intermediate fields. -/
theorem fixedFieldMultiplicity_cyclic_relation
    (H : Subgroup (E ≃ₐ[F] E)) (b : CyclicSubgroups H → ℤ)
    (hb : ∀ g : E ≃ₐ[F] E,
      (∑ C, (b C : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ C.val.map H.subtype)).character g) =
      Fintype.card H * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ H)).character g)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∑ C, b C * fixedFieldMultiplicity β (C.val.map H.subtype)) =
      Fintype.card H * fixedFieldMultiplicity β H := by
  let S : Option (CyclicSubgroups H) → Subgroup (E ≃ₐ[F] E)
    | none => H
    | some C => C.val.map H.subtype
  let c : Option (CyclicSubgroups H) → ℤ
    | none => -(Fintype.card H : ℤ)
    | some C => b C
  have hc : ∀ g, (∑ i, (c i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
      ((E ≃ₐ[F] E) ⧸ S i)).character g) = 0 := by
    intro g
    simp only [Fintype.sum_option, S, c, Int.cast_neg, Int.cast_natCast]
    rw [hb]
    ring
  have h := fixedFieldMultiplicity_relation S c hc hβ0 hβ1
  simp only [Fintype.sum_option, S, c] at h
  linarith

end DukePrimeDegree

end

end OAI
