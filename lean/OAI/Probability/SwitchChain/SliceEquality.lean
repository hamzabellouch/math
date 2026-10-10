import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceEquality

def equalityIndicator {α : Type*} (x : α → ℝ) (i j : α) : ℝ := by
  classical
  exact if x i = x j then 1 else 0

def centeredEquality {α : Type*} (x : α → ℝ) (p : ℝ) (i j : α) : ℝ :=
  equalityIndicator x i j - p

def offDiagonal {α : Type*} [DecidableEq α] (z : α → α → ℝ) (i j : α) : ℝ :=
  if i = j then 0 else z i j

theorem equalityIndicator_polynomial
    {α : Type*} (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (i j : α) :
    equalityIndicator x i j = 1 - x i - x j + 2 * x i * x j := by
  rcases hbinary i with hi | hi <;> rcases hbinary j with hj | hj <;>
    norm_num [equalityIndicator, hi, hj]

theorem centeredEquality_polynomial
    {α : Type*} (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (p : ℝ) (i j : α) :
    centeredEquality x p i j = (1 - p - x i) - x j + (2 * x i) * x j := by
  rw [centeredEquality, equalityIndicator_polynomial x hbinary]
  ring

theorem centeredEquality_symmetric
    {α : Type*} (x : α → ℝ) (p : ℝ) (i j : α) :
    centeredEquality x p i j = centeredEquality x p j i := by
  simp [centeredEquality, equalityIndicator, eq_comm]

theorem offDiagonal_symmetric
    {α : Type*} [DecidableEq α] (z : α → α → ℝ)
    (hsymm : ∀ i j, z i j = z j i) (i j : α) :
    offDiagonal z i j = offDiagonal z j i := by
  simp [offDiagonal, eq_comm, hsymm]

theorem sum_offDiagonal
    {α : Type*} [Fintype α] [DecidableEq α] (z : α → α → ℝ) (i : α) :
    (∑ j, offDiagonal z i j) = (∑ j, z i j) - z i i := by
  have hterm (j : α) : offDiagonal z i j = z i j - if i = j then z i i else 0 := by
    by_cases hij : i = j
    · subst j
      simp [offDiagonal]
    · simp [offDiagonal, hij]
  simp_rw [hterm]
  simp [Finset.sum_sub_distrib]

theorem centeredEquality_row_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (q p : ℝ) (hsum : ∑ j, x j = q) (i : α) :
    (∑ j, offDiagonal (centeredEquality x p) i j) =
      ((Fintype.card α : ℝ) - q - 1) - ((Fintype.card α : ℝ) - 1) * p +
        (2 * q - (Fintype.card α : ℝ)) * x i := by
  rw [sum_offDiagonal]
  have hdiag : centeredEquality x p i i = 1 - p := by
    simp [centeredEquality, equalityIndicator]
  rw [hdiag]
  simp_rw [centeredEquality_polynomial x hbinary]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hsum]
  ring

theorem additive_coeff_pairing
    {α : Type*} [Fintype α]
    (u : α → ℝ) (z : α → α → ℝ) (hsymm : ∀ i j, z i j = z j i) :
    (1 / 2 : ℝ) * (∑ i, ∑ j, (u i + u j) * z i j) =
      ∑ i, u i * (∑ j, z i j) := by
  have htranspose : (∑ i, ∑ j, u j * z i j) = ∑ i, ∑ j, u i * z i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsymm j i]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [htranspose]
  simp_rw [← Finset.mul_sum]
  ring

theorem additive_centeredEquality_image
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (q p : ℝ) (hsum : ∑ j, x j = q)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    (1 / 2 : ℝ) *
      (∑ i, ∑ j, (u i + u j) * offDiagonal (centeredEquality x p) i j) =
      (2 * q - (Fintype.card α : ℝ)) * (∑ i, u i * x i) := by
  rw [additive_coeff_pairing u _
    (offDiagonal_symmetric _ (centeredEquality_symmetric x p))]
  simp_rw [centeredEquality_row_sum x hbinary q p hsum]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hu, zero_mul, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem centeredEquality_total
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (q p : ℝ) (hsum : ∑ j, x j = q) :
    (∑ i, ∑ j, offDiagonal (centeredEquality x p) i j) =
      q * (q - 1) + ((Fintype.card α : ℝ) - q) * ((Fintype.card α : ℝ) - q - 1) -
        (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) * p := by
  simp_rw [centeredEquality_row_sum x hbinary q p hsum]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, hsum]
  ring

theorem centeredEquality_total_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 2 ≤ Fintype.card α)
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (q : ℝ) (hsum : ∑ j, x j = q) :
    (∑ i, ∑ j, offDiagonal
      (centeredEquality x
        ((q * (q - 1) + ((Fintype.card α : ℝ) - q) * ((Fintype.card α : ℝ) - q - 1)) /
          ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)))) i j) = 0 := by
  rw [centeredEquality_total x hbinary q _ hsum]
  have hc : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hcard
  have hn : (Fintype.card α : ℝ) ≠ 0 := by linarith
  have hm : (Fintype.card α : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

theorem row_zero_centeredEquality_image
    {α : Type*} [Fintype α]
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (p : ℝ) (c : α → α → ℝ)
    (hrow : ∀ i, ∑ j, c i j = 0) (hcol : ∀ j, ∑ i, c i j = 0) :
    (∑ i, ∑ j, c i j * centeredEquality x p i j) =
      2 * (∑ i, ∑ j, c i j * (x i * x j)) := by
  have hconstant : (∑ i, ∑ j, c i j * (1 - p)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.sum_mul, hrow, zero_mul]
  have hleft : (∑ i, ∑ j, c i j * x i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.sum_mul, hrow, zero_mul]
  have hright : (∑ i, ∑ j, c i j * x j) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    rw [← Finset.sum_mul, hcol, zero_mul]
  calc
    _ = ∑ i, ∑ j,
        (c i j * (1 - p) - c i j * x i - c i j * x j +
          2 * (c i j * (x i * x j))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [centeredEquality_polynomial x hbinary]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hconstant, hleft, hright]
      ring

theorem row_zero_offDiagonal_centeredEquality_image
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (p : ℝ) (c : α → α → ℝ) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, ∑ j, c i j = 0) (hcol : ∀ j, ∑ i, c i j = 0) :
    (1 / 2 : ℝ) * (∑ i, ∑ j, c i j * offDiagonal (centeredEquality x p) i j) =
      ∑ i, ∑ j, c i j * (x i * x j) := by
  have hterm (i j : α) :
      c i j * offDiagonal (centeredEquality x p) i j =
        c i j * centeredEquality x p i j := by
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · simp [offDiagonal, hij]
  simp_rw [hterm]
  rw [row_zero_centeredEquality_image x hbinary p c hrow hcol]
  ring

end Problem315.SliceEquality

end

end OAI
