import OAI.NumberTheory.Ostmann.Characters.BonamiCube

namespace OAI

/-! # Tensorizing the two-point Bonami estimate on a finite cube -/

namespace Ostmann

open Finset
open scoped Classical BigOperators

universe u

noncomputable def booleanMoment {α : Type*} [Fintype α]
    (l : ℕ) (a : (α → Bool) → ℝ) : ℝ :=
  ∑ ε : α → Bool, |booleanPolynomial a ε| ^ (2 * l)

theorem booleanMoment_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (l : ℕ) (a : (β → Bool) → ℝ) :
    booleanMoment l a =
      booleanMoment l (fun b : α → Bool => a (fun i => b (e.symm i))) := by
  unfold booleanMoment
  rw [← (Equiv.arrowCongr e (Equiv.refl Bool)).sum_comp]
  apply sum_congr rfl
  intro ε hε
  rw [booleanPolynomial_reindex e]
  simp [Equiv.arrowCongr]

theorem booleanMoment_option {α : Type*} [Fintype α]
    (l : ℕ) (a : (Option α → Bool) → ℝ) :
    booleanMoment l a =
      ∑ ε : α → Bool,
        (|booleanPolynomial (fun b => a (fun i => i.elim false b)) ε +
          booleanPolynomial (fun b => a (fun i => i.elim true b)) ε| ^ (2 * l) +
        |booleanPolynomial (fun b => a (fun i => i.elim false b)) ε -
          booleanPolynomial (fun b => a (fun i => i.elim true b)) ε| ^ (2 * l)) := by
  unfold booleanMoment
  have hs := sum_option_cube (fun ε : Option α → Bool =>
    |booleanPolynomial a ε| ^ (2 * l))
  simp only [finite_univ_canonical] at hs ⊢
  rw [hs, ← sum_add_distrib]
  apply sum_congr rfl
  intro ε hε
  simp only [booleanPolynomial_option, Option.elim, Bool.false_eq_true,
    ↓reduceIte, one_mul, neg_one_mul, sub_eq_add_neg]

/-- The exact weighted even-moment bound for arbitrary finite Boolean cubes. -/
theorem booleanPolynomial_moment (l : ℕ) (hl : 0 < l)
    (α : Type u) [Fintype α] (a : (α → Bool) → ℝ) :
    booleanMoment l a ≤ (Fintype.card (α → Bool) : ℝ) *
      booleanEnergy ((2 * l - 1 : ℕ) : ℝ) a ^ l := by
  let r : ℝ := ((2 * l - 1 : ℕ) : ℝ)
  have hr : 0 ≤ r := Nat.cast_nonneg _
  revert a
  refine Fintype.induction_empty_option
    (P := fun β _ => ∀ a : (β → Bool) → ℝ,
      booleanMoment l a ≤ (Fintype.card (β → Bool) : ℝ) * booleanEnergy r a ^ l)
    ?_ ?_ ?_ α
  · intro β γ instγ e ih a
    let : Fintype β := Fintype.ofEquiv γ e.symm
    rw [booleanMoment_reindex e, booleanEnergy_reindex e]
    rw [← Fintype.card_congr (Equiv.arrowCongr e (Equiv.refl Bool))]
    exact ih _
  · intro a
    simp [booleanMoment, booleanPolynomial, booleanEnergy, pow_mul, sq_abs]
  · intro β instβ ih a
    let a0 : (β → Bool) → ℝ := fun b => a (fun i => i.elim false b)
    let a1 : (β → Bool) → ℝ := fun b => a (fun i => i.elim true b)
    let E0 := booleanEnergy r a0
    let E1 := booleanEnergy r a1
    have hE0 : 0 ≤ E0 := booleanEnergy_nonneg r hr a0
    have hE1 : 0 ≤ E1 := booleanEnergy_nonneg r hr a1
    have h0 : (∑ ε : β → Bool, (booleanPolynomial a0 ε ^ 2) ^ l) ≤
        (Fintype.card (β → Bool) : ℝ) * E0 ^ l := by
      simpa only [booleanMoment, pow_mul, sq_abs] using ih a0
    have h1 : (∑ ε : β → Bool, (r * booleanPolynomial a1 ε ^ 2) ^ l) ≤
        (Fintype.card (β → Bool) : ℝ) * (r * E1) ^ l := by
      have hi1 : (∑ ε : β → Bool, (booleanPolynomial a1 ε ^ 2) ^ l) ≤
          (Fintype.card (β → Bool) : ℝ) * E1 ^ l := by
        simpa only [booleanMoment, pow_mul, sq_abs] using ih a1
      have hh := mul_le_mul_of_nonneg_left hi1 (pow_nonneg hr l)
      simpa only [mul_pow, ← mul_sum, mul_assoc, mul_left_comm] using hh
    have hmean := sum_add_pow_bound (univ : Finset (β → Bool))
      (fun ε => booleanPolynomial a0 ε ^ 2)
      (fun ε => r * booleanPolynomial a1 ε ^ 2) E0 (r * E1)
      hE0 (mul_nonneg hr hE1) (fun _ _ => sq_nonneg _)
      (fun _ _ => mul_nonneg hr (sq_nonneg _)) l hl h0 h1
    have hpoint (ε : β → Bool) :
        |booleanPolynomial a0 ε + booleanPolynomial a1 ε| ^ (2 * l) +
          |booleanPolynomial a0 ε - booleanPolynomial a1 ε| ^ (2 * l) ≤
        2 * (booleanPolynomial a0 ε ^ 2 + r * booleanPolynomial a1 ε ^ 2) ^ l := by
      have hh := bonami_two_point (booleanPolynomial a0 ε) (booleanPolynomial a1 ε) l hl
      dsimp only [r]
      linarith
    calc
      booleanMoment l a = ∑ ε : β → Bool,
          (|booleanPolynomial a0 ε + booleanPolynomial a1 ε| ^ (2 * l) +
          |booleanPolynomial a0 ε - booleanPolynomial a1 ε| ^ (2 * l)) :=
        booleanMoment_option l a
      _ ≤ ∑ ε : β → Bool,
          2 * (booleanPolynomial a0 ε ^ 2 + r * booleanPolynomial a1 ε ^ 2) ^ l :=
        sum_le_sum (fun ε _ => hpoint ε)
      _ = 2 * ∑ ε : β → Bool,
          (booleanPolynomial a0 ε ^ 2 + r * booleanPolynomial a1 ε ^ 2) ^ l :=
        (mul_sum ..).symm
      _ ≤ 2 * ((Fintype.card (β → Bool) : ℝ) * (E0 + r * E1) ^ l) := by
        exact mul_le_mul_of_nonneg_left hmean (by norm_num)
      _ = (Fintype.card (Option β → Bool) : ℝ) * booleanEnergy r a ^ l := by
        rw [booleanEnergy_option]
        have hcard := Fintype.card_congr
          (Equiv.piOptionEquivProd (β := fun _ : Option β => Bool))
        rw [Fintype.card_prod, Fintype.card_bool] at hcard
        rw [hcard, Nat.cast_mul, Nat.cast_ofNat]
        change 2 * ((Fintype.card (β → Bool) : ℝ) * (E0 + r * E1) ^ l) =
          2 * (Fintype.card (β → Bool) : ℝ) * (E0 + r * E1) ^ l
        ring
    simp only [Fintype.card, finite_univ_canonical, le_refl]

end Ostmann

end OAI
