import OAI.Analysis.KadisonKastler.FiniteMatrixInjectivity

namespace OAI

/-! # The projection associated with two commuting matrix actions

This is the finite-matrix formula for Haagerup's central-vector projection:
the normalized sum of matching left and conjugate-right matrix units.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (E F : MatrixUnitSystem ι (H →L[ℂ] H))

def pairedMatrixProjection : H →L[ℂ] H :=
  (Fintype.card ι : ℂ)⁻¹ • ∑ i, ∑ j, E.entry i j * F.entry i j

omit [Nonempty ι] in
theorem pairedMatrixSum_left (a b : ι) :
    E.entry a b * (∑ i, ∑ j, E.entry i j * F.entry i j) =
      ∑ j, E.entry a j * F.entry b j := by
  simp only [Finset.mul_sum, ← mul_assoc, E.mul_entry, ite_mul, zero_mul]
  simp

omit [Nonempty ι] in
theorem pairedMatrixSum_right
    (hcomm : ∀ i j k l, Commute (E.entry i j) (F.entry k l)) (a b : ι) :
    F.entry b a * (∑ i, ∑ j, E.entry i j * F.entry i j) =
      ∑ j, E.entry a j * F.entry b j := by
  have he (i j : ι) :
      F.entry b a * (E.entry i j * F.entry i j) =
        E.entry i j * (F.entry b a * F.entry i j) := by
    rw [← mul_assoc, ← (hcomm i j b a).eq, mul_assoc]
  simp only [Finset.mul_sum, he, F.mul_entry, mul_ite, mul_zero]
  simp

omit [Nonempty ι] in
theorem pairedMatrixProjection_intertwines
    (hcomm : ∀ i j k l, Commute (E.entry i j) (F.entry k l)) (a b : ι) :
    E.entry a b * pairedMatrixProjection E F = F.entry b a * pairedMatrixProjection E F := by
  simp only [pairedMatrixProjection, mul_smul_comm]
  rw [pairedMatrixSum_left, pairedMatrixSum_right E F hcomm]

omit [Nonempty ι] in
theorem pairedMatrixProjection_selfAdjoint
    (hcomm : ∀ i j k l, Commute (E.entry i j) (F.entry k l)) :
    IsSelfAdjoint (pairedMatrixProjection E F) := by
  change star (pairedMatrixProjection E F) = pairedMatrixProjection E F
  simp only [pairedMatrixProjection, star_smul, star_inv₀, star_natCast, star_sum,
    star_mul, E.star_entry, F.star_entry]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (hcomm i j i j).eq.symm

theorem pairedMatrixProjection_fixed (ξ : H)
    (hξ : ∀ i j, E.entry i j ξ = F.entry j i ξ) :
    pairedMatrixProjection E F ξ = ξ := by
  have he (i j : ι) : (E.entry i j * F.entry i j) ξ = E.entry i i ξ := by
    rw [mul_apply_eq_comp, ← hξ j i]
    change (E.entry i j * E.entry j i) ξ = _
    rw [E.mul_entry, ite_eq_left rfl]
  change (Fintype.card ι : ℂ)⁻¹ • ((∑ i, ∑ j, E.entry i j * F.entry i j) ξ) = ξ
  simp only [sum_apply, he, Finset.sum_const]
  rw [← Finset.smul_sum, ← sum_apply, E.total, one_apply_eq_self]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Finset.card_univ,
    inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero

end

end KadisonKastler

end OAI
