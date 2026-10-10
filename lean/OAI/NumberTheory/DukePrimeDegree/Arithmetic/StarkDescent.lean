import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ZeroPropagation
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.StarkAverage

namespace OAI

/-!
# Odd-index descent of a simple zero

Cyclic Hecke factorizations supply the real characters used by Stark's
odd-degree argument. The zero order on any fixed field is an average of
signs and is therefore at most one. A positive order at an odd-index
subgroup is incompatible with a nonvanishing rational zeta function.
-/

noncomputable section
open scoped NumberField BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

variable {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E]
variable [NumberField.IsTotallyReal E]
local instance starkDescentFintype : Fintype (E ≃ₐ[ℚ] E) := Fintype.ofFinite _

/-- The cyclic character data bounds every actual fixed-field order. -/
theorem fixedFieldMultiplicity_le_one_of_cyclic_characters
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hcyclic : ∀ C : Subgroup (E ≃ₐ[ℚ] E), IsCyclic C → ∃ χ : C →* ℝˣ,
      (∀ x : C, fixedFieldMultiplicity β (Subgroup.zpowers (x : E ≃ₐ[ℚ] E)) =
        if χ x = 1 then 1 else 0) ∧
      fixedFieldMultiplicity β C = if χ = 1 then 1 else 0)
    (H : Subgroup (E ≃ₐ[ℚ] E)) : fixedFieldMultiplicity β H ≤ 1 := by
  let m : Subgroup (E ≃ₐ[ℚ] E) → ℤ := fixedFieldMultiplicity β
  have havg := sum_eq_fixedFieldMultiplicity_of_cyclic_averages
    (fun g : E ≃ₐ[ℚ] E => (cyclicZeroSign m g : ℝ)) hβ0 hβ1
    (fun C hC => by
      obtain ⟨χ, hχ, hprincipal⟩ := hcyclic C hC
      exact sum_cyclicZeroSign m C χ hχ hprincipal) H
  have hbound : (∑ g : H, (cyclicZeroSign m (g : E ≃ₐ[ℚ] E) : ℝ)) ≤
      Fintype.card H := by
    calc
      _ ≤ ∑ _g : H, (1 : ℝ) := Finset.sum_le_sum (fun g _ => by
        unfold cyclicZeroSign
        split_ifs <;> norm_num)
      _ = Fintype.card H := by simp
  rw [havg] at hbound
  have hcard : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have hreal : (fixedFieldMultiplicity β H : ℝ) ≤ 1 := by nlinarith
  exact_mod_cast hreal

theorem no_odd_index_positive_zero_of_cyclic_characters
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hcyclic : ∀ C : Subgroup (E ≃ₐ[ℚ] E), IsCyclic C → ∃ χ : C →* ℝˣ,
      (∀ x : C, fixedFieldMultiplicity β (Subgroup.zpowers (x : E ≃ₐ[ℚ] E)) =
        if χ x = 1 then 1 else 0) ∧
      fixedFieldMultiplicity β C = if χ = 1 then 1 else 0)
    (H : Subgroup (E ≃ₐ[ℚ] E)) (hodd : Odd H.index)
    (hH : 0 < fixedFieldMultiplicity β H) (hQ : zetaMultiplicity ℚ β = 0) : False := by
  have hbound := fixedFieldMultiplicity_le_one_of_cyclic_characters hβ0 hβ1 hcyclic H
  have hone : fixedFieldMultiplicity β H = 1 := by omega
  exact no_odd_index_zero_sign hβ0 hβ1 hcyclic H hodd hone
    ((fixedFieldMultiplicity_top_eq hβ0 hβ1).trans hQ)

/-- Even ray realizations of each cyclic subgroup's Frobenius characters. -/
def HasCyclicRayRealizations (E : Type*) [Field E] [NumberField E] [IsGalois ℚ E] : Prop :=
  ∀ (C : Subgroup (E ≃ₐ[ℚ] E)), IsCyclic C →
    ∃ N : ℕ, 0 < N ∧ (NumberField.discr E).natAbs ∣ N ∧
      ∃ ψ : ((E ≃ₐ[IntermediateField.fixedField C] E) →* ℂˣ) →
        EvenRayCharacter (IntermediateField.fixedField C) N,
        (∀ χ, (ψ χ).idealHom = idealHom (IntermediateField.fixedField C) E χ) ∧
        ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal

/-- Propagation to the extension is obtained from actual cyclic factors. -/
theorem extension_multiplicity_pos_of_ray_realizations
    (hray : HasCyclicRayRealizations E)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (H : Subgroup (E ≃ₐ[ℚ] E)) (hH : 0 < fixedFieldMultiplicity β H) :
    0 < zetaMultiplicity E β := by
  apply extension_multiplicity_pos_of_fixedField_pos hβ0 hβ1 _ H hH
  intro C hC
  let := hC
  obtain ⟨N, hN, hD, ψ, hid, hψ⟩ := hray C hC
  let : NeZero N := ⟨hN.ne'⟩
  exact fixedFieldMultiplicity_le_extension C ψ hid hψ hD hβ0 hβ1

theorem cyclic_character_of_ray_realizations
    (hray : HasCyclicRayRealizations E)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hsimple : zetaMultiplicity E β = 1)
    (C : Subgroup (E ≃ₐ[ℚ] E)) (hC : IsCyclic C) :
    ∃ χ : C →* ℝˣ,
      (∀ x : C, fixedFieldMultiplicity β (Subgroup.zpowers (x : E ≃ₐ[ℚ] E)) =
        if χ x = 1 then 1 else 0) ∧
      fixedFieldMultiplicity β C = if χ = 1 then 1 else 0 := by
  let := hC
  obtain ⟨N, hN, hD, ψ, hid, hψ⟩ := hray C hC
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨χ, hχ, hp⟩ := cyclic_fixedField_character
    (E := E) (N := N) (β := β) C ψ hid hψ hD hβ0 hβ1 hsimple
  refine ⟨χ, ?_, ?_⟩
  · intro x
    by_cases hx : χ x = 1
    · simpa only [hx, ite_true] using hχ x
    · simpa only [hx, ite_false] using hχ x
  · by_cases hx : χ = 1
    · simpa only [hx, ite_true] using hp
    · simpa only [hx, ite_false] using hp

/-- The final finite Galois descent, before choosing a normal closure. -/
theorem no_odd_index_zero_of_ray_realizations
    (hray : HasCyclicRayRealizations E)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hsimple : zetaMultiplicity E β = 1)
    (H : Subgroup (E ≃ₐ[ℚ] E)) (hodd : Odd H.index)
    (hH : 0 < fixedFieldMultiplicity β H) (hQ : zetaMultiplicity ℚ β = 0) : False := by
  exact no_odd_index_positive_zero_of_cyclic_characters hβ0 hβ1
    (cyclic_character_of_ray_realizations hray hβ0 hβ1 hsimple) H hodd hH hQ

end DukePrimeDegree

end

end OAI
