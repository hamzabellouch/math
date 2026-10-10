import OAI.Analysis.KadisonKastler.FaithfulTraceGNS

namespace OAI

/-! # Centered letters for the finite-diagonal free-product representation

These are the coefficient and covariance identities used to construct the
creation operators in the Ricard--Xu representation. No word-norm estimate
or free-product representation is assumed.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {B ι α : Type*} [CStarAlgebra B] [Fintype α] [DecidableEq α]
  (e : ι → α → B)

def diagonalLinearCombination (i : ι) (c : α → ℂ) : B := ∑ a, c a • e i a

omit [Fintype α] in
theorem diagonal_projection_product
    (hp : ∀ i a, IsStarProjection (e i a))
    (ho : ∀ i a b, a ≠ b → e i a * e i b = 0)
    (i : ι) (a b : α) : e i a * e i b = if a = b then e i a else 0 := by
  split_ifs with h
  · subst b
    exact (hp i a).isIdempotentElem.eq
  · exact ho i a b h

theorem diagonalLinearCombination_mul
    (hp : ∀ i a, IsStarProjection (e i a))
    (ho : ∀ i a b, a ≠ b → e i a * e i b = 0)
    (i : ι) (c f : α → ℂ) :
    diagonalLinearCombination e i c * diagonalLinearCombination e i f =
      diagonalLinearCombination e i (fun a => c a * f a) := by
  classical
  simp only [diagonalLinearCombination, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, diagonal_projection_product e hp ho]
  apply Finset.sum_congr rfl
  intro a _
  simp [smul_smul, mul_comm]

omit [DecidableEq α] in
theorem star_diagonalLinearCombination (hp : ∀ i a, IsStarProjection (e i a))
    (i : ι) (c : α → ℂ) :
    star (diagonalLinearCombination e i c) =
      diagonalLinearCombination e i (fun a => star (c a)) := by
  simp only [diagonalLinearCombination, star_sum, star_smul,
    (hp _ _).isSelfAdjoint.star_eq]

omit [DecidableEq α] in
theorem trace_diagonalLinearCombination (τ : FaithfulTracialState B) (t : ℂ)
    (ht : ∀ i a, τ.toLinearMap (e i a) = t) (i : ι) (c : α → ℂ) :
    τ.toLinearMap (diagonalLinearCombination e i c) = (∑ a, c a) * t := by
  simp only [diagonalLinearCombination, map_sum, map_smul, ht, smul_eq_mul,
    Finset.sum_mul]

variable [Nonempty α]

def diagonalCentered (i : ι) (a : α) : B :=
  e i a - (Fintype.card α : ℂ)⁻¹ • 1

def diagonalCenteredCoefficient (a b : α) : ℂ :=
  (if b = a then 1 else 0) - (Fintype.card α : ℂ)⁻¹

theorem sum_diagonalCenteredCoefficient (a : α) :
    ∑ b, diagonalCenteredCoefficient a b = 0 := by
  classical
  simp [diagonalCenteredCoefficient, Finset.sum_sub_distrib, nsmul_eq_mul,
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero]

omit [Nonempty α] in
theorem diagonalCentered_eq_linearCombination (hs : ∀ i, ∑ a, e i a = 1)
    (i : ι) (a : α) :
    diagonalCentered e i a = diagonalLinearCombination e i (diagonalCenteredCoefficient a) := by
  classical
  simp only [diagonalLinearCombination, diagonalCenteredCoefficient, sub_smul,
    Finset.sum_sub_distrib, ← Finset.smul_sum, hs, diagonalCentered]
  simp

omit [DecidableEq α] [Nonempty α] in
theorem star_diagonalCentered (hp : ∀ i a, IsStarProjection (e i a))
    (i : ι) (a : α) : star (diagonalCentered e i a) = diagonalCentered e i a := by
  simp [diagonalCentered, star_smul, (hp i a).isSelfAdjoint.star_eq]

omit [DecidableEq α] [Nonempty α] in
theorem trace_diagonalCentered (τ : FaithfulTracialState B)
    (ht : ∀ i a, τ.toLinearMap (e i a) = (Fintype.card α : ℂ)⁻¹)
    (i : ι) (a : α) : τ.toLinearMap (diagonalCentered e i a) = 0 := by
  simp [diagonalCentered, ht, τ.map_one]

omit [Nonempty α] in
theorem trace_diagonalCentered_covariance (τ : FaithfulTracialState B)
    (hp : ∀ i a, IsStarProjection (e i a))
    (ho : ∀ i a b, a ≠ b → e i a * e i b = 0)
    (ht : ∀ i a, τ.toLinearMap (e i a) = (Fintype.card α : ℂ)⁻¹)
    (i : ι) (a b : α) :
    τ.toLinearMap (star (diagonalCentered e i a) * diagonalCentered e i b) =
      (Fintype.card α : ℂ)⁻¹ *
        ((if a = b then 1 else 0) - (Fintype.card α : ℂ)⁻¹) := by
  rw [star_diagonalCentered e hp]
  simp only [diagonalCentered, sub_mul, mul_sub, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one,
    diagonal_projection_product e hp ho]
  by_cases h : a = b
  · simp only [h, ite_true, map_sub, map_smul, ht, τ.map_one, smul_eq_mul]
    ring
  · simp only [h, ite_false, map_sub, map_zero, map_smul, ht, τ.map_one, smul_eq_mul]
    ring

omit [Nonempty α] in
theorem diagonalCentered_mul
    (hp : ∀ i a, IsStarProjection (e i a))
    (ho : ∀ i a b, a ≠ b → e i a * e i b = 0)
    (i : ι) (a b : α) :
    diagonalCentered e i a * diagonalCentered e i b =
      ((if a = b then 1 else 0) - (Fintype.card α : ℂ)⁻¹) • diagonalCentered e i a -
      (Fintype.card α : ℂ)⁻¹ • diagonalCentered e i b +
      ((Fintype.card α : ℂ)⁻¹ *
        ((if a = b then 1 else 0) - (Fintype.card α : ℂ)⁻¹)) • (1 : B) := by
  classical
  simp only [diagonalCentered, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_sub, smul_smul, diagonal_projection_product e hp ho]
  split_ifs <;> module

end

end KadisonKastler

end OAI
