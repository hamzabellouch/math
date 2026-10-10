import OAI.NumberTheory.DirichletL.IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality

namespace OAI

namespace SevenEighths.RayOrthogonality

open scoped Classical
noncomputable section

section FiniteMonoid
variable {R : Type*} [CommMonoid R] [Finite R]

def characters (H : Subgroup Rˣ) : Subgroup (MulChar R ℂ) :=
  (MulChar.subgroupOrderIsoSubgroupMulChar R ℂ H).ofDual

instance (H : Subgroup Rˣ) : Fintype (characters H) := Fintype.ofFinite _

theorem mem_characters_iff (H : Subgroup Rˣ) (χ : MulChar R ℂ) :
    χ ∈ characters H ↔ ∀ u ∈ H, χ u = 1 :=
  MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff

theorem card_characters (H : Subgroup Rˣ) :
    Fintype.card (characters H) = Nat.card (Rˣ ⧸ H) := by
  rw [← Nat.card_eq_fintype_card]
  exact MulChar.card_subgroupOrderIsoSubgroupMulChar

theorem exists_character_ne_one (H : Subgroup Rˣ) {u : Rˣ} (hu : u ∉ H) :
    ∃ χ : characters H, (χ : MulChar R ℂ) u ≠ 1 := by
  by_contra hn
  apply hu
  have hall : ∀ χ ∈ characters H, χ u = 1 := by
    intro χ hχ
    by_contra h
    exact hn ⟨⟨χ, hχ⟩, h⟩
  have hh := (MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff).mpr hall
  simpa only [characters, OrderDual.toDual_ofDual, OrderIso.symm_apply_apply] using hh

theorem sum_characters_unit (H : Subgroup Rˣ) (u : Rˣ) :
    ∑ χ : characters H, (χ : MulChar R ℂ) u =
      if u ∈ H then (Nat.card (Rˣ ⧸ H) : ℂ) else 0 := by
  by_cases hu : u ∈ H
  · simp only [hu, ite_true]
    calc
      _ = ∑ _χ : characters H, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro χ _
        exact (mem_characters_iff H χ).mp χ.property u hu
      _ = _ := by simp [card_characters]
  · simp only [hu, ite_false]
    obtain ⟨χ, hχ⟩ := exists_character_ne_one H hu
    refine eq_zero_of_mul_eq_self_left hχ ?_
    simp only [Finset.mul_sum, ← MulChar.mul_apply]
    exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' ↦ rfl

def inUnitSubgroup (H : Subgroup Rˣ) (r : R) : Prop :=
  ∃ u : Rˣ, (u : R) = r ∧ u ∈ H

theorem sum_characters (H : Subgroup Rˣ) (r : R) :
    ∑ χ : characters H, (χ : MulChar R ℂ) r =
      if inUnitSubgroup H r then (Nat.card (Rˣ ⧸ H) : ℂ) else 0 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    have hi : inUnitSubgroup H (u : R) ↔ u ∈ H := by
      constructor
      · rintro ⟨v, hv, h⟩
        exact (Units.ext hv) ▸ h
      · exact fun h ↦ ⟨u, rfl, h⟩
    rw [sum_characters_unit, hi]
  · have hn : ¬ inUnitSubgroup H r := by
      rintro ⟨u, rfl, _⟩
      exact hr u.isUnit
    simp only [hn, ite_false]
    exact Finset.sum_eq_zero fun χ _ ↦ MulChar.map_nonunit χ.val hr

theorem ray_card_pos (H : Subgroup Rˣ) : 0 < Nat.card (Rˣ ⧸ H) :=
  Nat.card_pos

theorem average_characters (H : Subgroup Rˣ) (r : R) :
    (∑ χ : characters H, (χ : MulChar R ℂ) r) / (Nat.card (Rˣ ⧸ H) : ℂ) =
      if inUnitSubgroup H r then 1 else 0 := by
  rw [sum_characters]
  have hn : (Nat.card (Rˣ ⧸ H) : ℂ) ≠ 0 := by
    exact_mod_cast (ray_card_pos H).ne'
  split_ifs <;> simp [hn]

end FiniteMonoid

section Residues
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]

def globalUnits : Subgroup (A ⧸ M)ˣ :=
  (Units.map (Ideal.Quotient.mk M).toMonoidHom).range

abbrev rayCharacters := characters (globalUnits M)

theorem mem_rayCharacters_iff (χ : MulChar (A ⧸ M) ℂ) :
    χ ∈ rayCharacters M ↔ IdealCharacter.UnitInvariant M χ := by
  rw [mem_characters_iff]
  constructor
  · intro h u
    exact h _ ⟨u, rfl⟩
  · intro h u hu
    obtain ⟨v, rfl⟩ := hu
    exact h v

def principalResidue (r : A ⧸ M) : Prop :=
  ∃ u : Aˣ, Ideal.Quotient.mk M u = r

omit [Finite (A ⧸ M)] in
theorem inUnitSubgroup_globalUnits_iff (r : A ⧸ M) :
    inUnitSubgroup (globalUnits M) r ↔ principalResidue M r := by
  constructor
  · rintro ⟨u, hur, v, hv⟩
    exact ⟨v, (congrArg Units.val hv).trans hur⟩
  · rintro ⟨u, hu⟩
    exact ⟨Units.map (Ideal.Quotient.mk M).toMonoidHom u, hu, ⟨u, rfl⟩⟩

abbrev rayCard : ℕ := Nat.card ((A ⧸ M)ˣ ⧸ globalUnits M)

theorem rayCard_pos : 0 < rayCard M := ray_card_pos _

theorem sum_rayCharacters (r : A ⧸ M) :
    ∑ χ : rayCharacters M, (χ : MulChar (A ⧸ M) ℂ) r =
      if principalResidue M r then (rayCard M : ℂ) else 0 := by
  rw [sum_characters, inUnitSubgroup_globalUnits_iff]

theorem average_rayCharacters (r : A ⧸ M) :
    (∑ χ : rayCharacters M, (χ : MulChar (A ⧸ M) ℂ) r) / (rayCard M : ℂ) =
      if principalResidue M r then 1 else 0 := by
  rw [average_characters, inUnitSubgroup_globalUnits_iff]

section PrincipalIdeals
variable [IsDomain A] [IsPrincipalIdealRing A]

def idealCharacter (χ : rayCharacters M) : Ideal A →*₀ ℂ :=
  IdealCharacter.ofResidue M χ ((mem_rayCharacters_iff M χ).mp χ.property)

def principalIdeals : Set (Ideal A) :=
  {I | I ≠ ⊥ ∧ ∃ a : A, Ideal.span ({a} : Set A) = I ∧
    principalResidue M (Ideal.Quotient.mk M a)}

omit [Finite (A ⧸ M)] in
theorem principalIdeals_iff_generator {I : Ideal A} (hI : I ≠ ⊥) :
    I ∈ principalIdeals M ↔
      principalResidue M (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
  constructor
  · rintro ⟨_, a, ha, u, hu⟩
    have hga : Associated (Submodule.IsPrincipal.generator I) a := by
      rw [← ha]
      exact Submodule.IsPrincipal.associated_generator_span_self a
    obtain ⟨v, hv⟩ := hga
    refine ⟨u * v⁻¹, ?_⟩
    have hq := congrArg (Ideal.Quotient.mk M) hv
    simp only [map_mul] at hq
    simp only [Units.val_mul, map_mul]
    rw [hu, ← hq]
    rw [mul_assoc, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, mul_one]
  · intro h
    exact ⟨hI, _, Ideal.span_singleton_generator I, h⟩

omit [Finite (A ⧸ M)] [IsPrincipalIdealRing A] in

theorem principalIdeals_iff_congruent_one (I : Ideal A) :
    I ∈ principalIdeals M ↔ ∃ a : A, a ≠ 0 ∧
      Ideal.span ({a} : Set A) = I ∧ Ideal.Quotient.mk M a = 1 := by
  constructor
  · rintro ⟨hI, a, ha, u, hu⟩
    refine ⟨a * (u⁻¹ : Aˣ), ?_, ?_, ?_⟩
    · apply mul_ne_zero
      · exact fun h ↦ hI (ha ▸ (Ideal.span_singleton_eq_bot.mpr h))
      · exact Units.ne_zero _
    · rw [Ideal.span_singleton_mul_right_unit (u⁻¹).isUnit, ha]
    · rw [map_mul, ← hu, ← map_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, map_one]
  · rintro ⟨a, ha, hI, hq⟩
    refine ⟨?_, a, hI, 1, ?_⟩
    · exact fun h ↦ ha (Ideal.span_singleton_eq_bot.mp (hI.trans h))
    · simpa only [Units.val_one, map_one] using hq.symm

theorem norm_idealCharacter_le_one (χ : rayCharacters M) (I : Ideal A) :
    ‖idealCharacter M χ I‖ ≤ 1 := IdealCharacter.norm_ofResidue_le_one M χ _ I

theorem idealCharacter_one (I : Ideal A) :
    idealCharacter M 1 I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 :=
  IdealCharacter.ofResidue_one M I

theorem sum_idealCharacters (I : Ideal A) :
    ∑ χ : rayCharacters M, idealCharacter M χ I =
      if I ∈ principalIdeals M then (rayCard M : ℂ) else 0 := by
  by_cases hI : I = ⊥
  · subst I
    simp [idealCharacter, principalIdeals]
  · have heq (χ : rayCharacters M) : idealCharacter M χ I =
        (χ : MulChar (A ⧸ M) ℂ) (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
      exact IdealCharacter.ofResidue_of_generator M χ _ hI (Ideal.span_singleton_generator I)
    simp only [heq, sum_rayCharacters, principalIdeals_iff_generator M hI]

theorem average_idealCharacters (I : Ideal A) :
    (∑ χ : rayCharacters M, idealCharacter M χ I) / (rayCard M : ℂ) =
      if I ∈ principalIdeals M then 1 else 0 := by
  rw [sum_idealCharacters]
  have hn : (rayCard M : ℂ) ≠ 0 := by exact_mod_cast (rayCard_pos M).ne'
  split_ifs <;> simp [hn]

end PrincipalIdeals
end Residues

end
end SevenEighths.RayOrthogonality

end OAI
