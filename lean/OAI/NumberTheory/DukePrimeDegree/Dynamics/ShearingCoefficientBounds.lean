import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingKappa
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingScale

namespace OAI

/-!
# Uniform bounds on the selected shearing interval

The logarithmic scale controls every coefficient of the quadratic
conjugation formula. A bound on `|t| * κ` therefore gives a uniform
matrix-displacement bound on the whole symmetric interval.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootShearingKappa_diagonal_bound {n : ℕ} (i j : Fin n) (g : G n) :
    |g.val j j - g.val i i| ≤ rootShearingKappa i j g := le_max_left _ _

lemma rootShearingKappa_quadratic_bound {n : ℕ} (i j : Fin n) (g : G n) :
    |g.val j i| ≤ (rootShearingKappa i j g) ^ 2 := by
  have hs : Real.sqrt |g.val j i| ≤ rootShearingKappa i j g :=
    (le_add_of_nonneg_right (rootShearingOffDiagonalSize_nonneg i j g)).trans (le_max_right _ _)
  nlinarith [Real.sq_sqrt (abs_nonneg (g.val j i)), Real.sqrt_nonneg |g.val j i|,
    rootShearingKappa_nonneg i j g]

lemma rootShearingKappa_offDiagonal_bound {n : ℕ} (i j : Fin n) (g : G n) :
    rootShearingOffDiagonalSize i j g ≤ rootShearingKappa i j g :=
  (le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans (le_max_right _ _)

lemma rootShearingKappa_row_bound {n : ℕ} {i j k : Fin n} (g : G n)
    (hkj : k ≠ j) (hsmall : rootShearingKappa i j g ≤ 1) :
    |g.val j k| ≤ rootShearingKappa i j g := by
  by_cases hki : k = i
  · subst k
    have hb := rootShearingKappa_quadratic_bound i j g
    nlinarith [rootShearingKappa_nonneg i j g]
  · exact (rootShearingOffDiagonalSize_row_bound hki hkj g).trans
      (rootShearingKappa_offDiagonal_bound i j g)

lemma rootShearingKappa_col_bound {n : ℕ} {i j k : Fin n} (g : G n)
    (hki : k ≠ i) (hsmall : rootShearingKappa i j g ≤ 1) :
    |g.val k i| ≤ rootShearingKappa i j g := by
  by_cases hkj : k = j
  · subst k
    have hb := rootShearingKappa_quadratic_bound i j g
    nlinarith [rootShearingKappa_nonneg i j g]
  · exact (rootShearingOffDiagonalSize_col_bound hki hkj g).trans
      (rootShearingKappa_offDiagonal_bound i j g)

lemma rootShearingKappa_linear_bound {n : ℕ} (i j r s : Fin n) (g : G n)
    (hsmall : rootShearingKappa i j g ≤ 1) :
    |(if r = i then g.val j s else 0) - (if s = j then g.val r i else 0)| ≤
      2 * rootShearingKappa i j g := by
  have hk := rootShearingKappa_nonneg i j g
  by_cases hr : r = i <;> by_cases hs : s = j
  · subst r; subst s
    simpa only [ite_true] using (rootShearingKappa_diagonal_bound i j g).trans
      (by linarith : rootShearingKappa i j g ≤ 2 * rootShearingKappa i j g)
  · subst r
    simp only [ite_true, hs, ite_false, sub_zero]
    exact (rootShearingKappa_row_bound g hs hsmall).trans (by linarith)
  · subst s
    simp only [hr, ite_false, ite_true, zero_sub, abs_neg]
    exact (rootShearingKappa_col_bound g hr hsmall).trans (by linarith)
  · simp only [hr, hs, ite_false, sub_zero, abs_zero]
    linarith

theorem rootShear_entry_bound_of_scale {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hsmall : rootShearingKappa i j g ≤ 1)
    (u C : ℝ) (hu : |u| * rootShearingKappa i j g ≤ C) (r s : Fin n) :
    |(Matrix.SpecialLinearGroup.transvection hij u * g *
      Matrix.SpecialLinearGroup.transvection hij (-u)).val r s - g.val r s| ≤ 2 * C + C ^ 2 := by
  let L := (if r = i then g.val j s else 0) - (if s = j then g.val r i else 0)
  let Q := if r = i ∧ s = j then g.val j i else 0
  have hL : |L| ≤ 2 * rootShearingKappa i j g := rootShearingKappa_linear_bound i j r s g hsmall
  have hQ : |Q| ≤ (rootShearingKappa i j g) ^ 2 := by
    dsimp [Q]
    split_ifs
    · exact rootShearingKappa_quadratic_bound i j g
    · simpa only [abs_zero] using sq_nonneg (rootShearingKappa i j g)
  have he : (Matrix.SpecialLinearGroup.transvection hij u * g *
      Matrix.SpecialLinearGroup.transvection hij (-u)).val r s - g.val r s = u * L - u ^ 2 * Q := by
    rw [root_conjugation_entry]
    dsimp [L, Q]
    split_ifs <;> ring
  have hk := rootShearingKappa_nonneg i j g
  have hC : 0 ≤ C := (mul_nonneg (abs_nonneg u) hk).trans hu
  have hlinear : |u| * |L| ≤ 2 * C := by
    have h := mul_le_mul_of_nonneg_left hL (abs_nonneg u)
    nlinarith
  have hquadratic : |u| ^ 2 * |Q| ≤ C ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hQ (sq_nonneg |u|)
    have hsq : (|u| * rootShearingKappa i j g) ^ 2 ≤ C ^ 2 := by
      nlinarith [mul_nonneg (abs_nonneg u) hk]
    nlinarith
  rw [he]
  have h := abs_sub_le (u * L) 0 (u ^ 2 * Q)
  simp only [sub_zero, zero_sub, abs_neg, abs_mul, abs_pow] at h
  linarith

theorem rootShearSize_bound_of_scale {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hsmall : rootShearingKappa i j g ≤ 1)
    (u C : ℝ) (hu : |u| * rootShearingKappa i j g ≤ C) :
    rootShearSize hij g u ≤ (n : ℝ) * n * (2 * C + C ^ 2) := by
  unfold rootShearSize
  calc
    _ ≤ ∑ _r : Fin n, ∑ _s : Fin n, (2 * C + C ^ 2) :=
      Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ =>
        rootShear_entry_bound_of_scale hij g hsmall u C hu r s
    _ = _ := by simp; ring

end DukePrimeDegree

end

end OAI
