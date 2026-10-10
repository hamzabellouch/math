import Mathlib.Data.Fintype.CardEmbedding
import OAI.Combinatorics.BalancedRyser.Local.Local

namespace OAI

namespace Balanced.Local

abbrev DirectionToken (b κ : ℕ) := Fin b ⊕ Fin (4 * b - κ)

def assignmentFunction {F : Type*} {b κ : ℕ} (a : DirectionAssignment F b κ) :
    DirectionToken b κ → Direction F := Sum.elim a.1 a.2

def AllTokensDistinct {F : Type*} {b κ : ℕ} (a : DirectionAssignment F b κ) : Prop :=
  Function.Injective (assignmentFunction a)

def tokenInjectionEquiv (F : Type*) (b κ : ℕ) :
    (DirectionToken b κ ↪ Direction F) ≃
      {a : DirectionAssignment F b κ // AllTokensDistinct a} where
  toFun e := ⟨(fun i => e (Sum.inl i), fun j => e (Sum.inr j)), by
    intro x y h
    apply e.injective
    cases x <;> cases y <;> exact h⟩
  invFun a := ⟨assignmentFunction a.val, a.property⟩
  left_inv e := by ext x; cases x <;> rfl
  right_inv a := by apply Subtype.ext; rfl

theorem allTokensDistinct_eligible {F : Type*} {b κ : ℕ}
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (ha : AllTokensDistinct a) : Eligible P a := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    have h' : Sum.inl i = (Sum.inl j : DirectionToken b κ) := ha h
    exact Sum.inl.inj h'
  · intro i j h
    have h' : Sum.inr i = (Sum.inr j : DirectionToken b κ) := ha h
    exact Sum.inr.inj h'
  · intro i j h
    have h' : Sum.inr (P.classOf i j) = (Sum.inl i : DirectionToken b κ) := ha h
    cases h'

theorem eligible_not_allTokensDistinct_iff {F : Type*} {b κ : ℕ}
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ) (ha : Eligible P a) :
    ¬ AllTokensDistinct a ↔ ∃ i j, a.1 i = a.2 j := by
  constructor
  · intro h
    by_contra hex
    apply h
    intro x y hxy
    cases x with
    | inl i =>
        cases y with
        | inl j => exact congrArg Sum.inl (ha.1 hxy)
        | inr j => exact False.elim (hex ⟨i, j, hxy⟩)
    | inr i =>
        cases y with
        | inl j => exact False.elim (hex ⟨j, i, hxy.symm⟩)
        | inr j => exact congrArg Sum.inr (ha.2.1 hxy)
  · rintro ⟨i, j, hij⟩ hd
    have h' : Sum.inl i = (Sum.inr j : DirectionToken b κ) := hd hij
    cases h'

theorem card_directionToken_two {b : ℕ} (hb : 1 ≤ b) :
    Fintype.card (DirectionToken b 2) = 5 * b - 2 := by
  simp only [DirectionToken, Fintype.card_sum, Fintype.card_fin]
  omega

section CrossEquality

variable {I G J : Type*} [Fintype I] [Fintype G] [Fintype J]
  [DecidableEq I] [DecidableEq G] [DecidableEq J]

def crossEqualityEquiv (i : I) (j : G) :
    {a : (I → J) × (G → J) // a.1 i = a.2 j} ≃
      (({k : I // k ≠ i} → J) × (G → J)) where
  toFun a := (fun k => a.val.1 k, a.val.2)
  invFun a := ⟨(fun k => if h : k = i then a.2 j else a.1 ⟨k, h⟩, a.2), by simp⟩
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · funext k
      by_cases hk : k = i
      · subst k; simp [a.property]
      · simp [hk]
    · rfl
  right_inv a := by
    apply Prod.ext
    · funext k
      simp [k.property]
    · rfl

theorem card_crossEquality (i : I) (j : G) :
    ((Finset.univ : Finset ((I → J) × (G → J))).filter
      (fun a => a.1 i = a.2 j)).card =
        Fintype.card J ^ (Fintype.card I - 1) * Fintype.card J ^ Fintype.card G := by
  have hsub : Fintype.card {k : I // k ≠ i} = Fintype.card I - 1 := by
    simpa only [Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun k : I => k = i)
  have h := Fintype.card_congr (crossEqualityEquiv (J := J) i j)
  simpa only [Fintype.card_subtype, Fintype.card_prod, Fintype.card_fun, hsub] using h

theorem card_any_crossEquality_le :
    ((Finset.univ : Finset ((I → J) × (G → J))).filter
      (fun a => ∃ i j, a.1 i = a.2 j)).card ≤
        (Fintype.card I * Fintype.card G) *
          (Fintype.card J ^ (Fintype.card I - 1) * Fintype.card J ^ Fintype.card G) := by
  classical
  let E (ij : I × G) := (Finset.univ : Finset ((I → J) × (G → J))).filter
    (fun a => a.1 ij.1 = a.2 ij.2)
  calc
    _ ≤ (Finset.univ.biUnion E).card := by
      apply Finset.card_le_card
      intro a ha
      obtain ⟨i, j, hij⟩ := (Finset.mem_filter.mp ha).2
      exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _, by simp [E, hij]⟩
    _ ≤ ∑ ij : I × G, (E ij).card := Finset.card_biUnion_le
    _ = _ := by
      simp only [E, card_crossEquality, Finset.sum_const, Finset.card_univ,
        Fintype.card_prod, smul_eq_mul]

end CrossEquality

section FiniteField

variable {F : Type*} [Fintype F]

open scoped Classical in

theorem card_eligible_not_allDistinct_two_le {b : ℕ} (hb : 1 ≤ b)
    (P : EqualityPattern b 2) :
    ((Finset.univ : Finset (DirectionAssignment F b 2)).filter
      (fun a => Eligible P a ∧ ¬ AllTokensDistinct a)).card ≤
        b * (4 * b - 2) * (Fintype.card F + 1) ^ (5 * b - 3) := by
  classical
  have hexp : (b - 1) + (4 * b - 2) = 5 * b - 3 := by omega
  calc
    _ ≤ ((Finset.univ : Finset (DirectionAssignment F b 2)).filter
        (fun a => ∃ i j, a.1 i = a.2 j)).card := by
      apply Finset.card_le_card
      intro a ha
      obtain ⟨_, ha, hnot⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (eligible_not_allTokensDistinct_iff P a ha).mp hnot⟩
    _ ≤ _ := by
      have h := card_any_crossEquality_le (I := Fin b) (G := Fin (4 * b - 2))
        (J := Direction F)
      simpa only [Fintype.card_fin, Direction, Fintype.card_option,
        ← pow_add, hexp] using h

theorem card_token_injections_two_le {b : ℕ} (hb : 1 ≤ b) :
    Fintype.card (DirectionToken b 2 ↪ Direction F) ≤
      (Fintype.card F + 1) ^ (5 * b - 2) := by
  have h : Fintype.card (DirectionToken b 2 ↪ Direction F) ≤
      Fintype.card (DirectionToken b 2 → Direction F) :=
    Fintype.card_le_of_injective _ Function.Embedding.coe_injective
  simpa only [Fintype.card_fun, card_directionToken_two hb,
    Direction, Fintype.card_option] using h

end FiniteField

end Balanced.Local

end OAI
