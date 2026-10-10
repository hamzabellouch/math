import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingProfile
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingCentralizer

namespace OAI

/-!
# The normalized profile of an actual return matrix

The algebraic profile is the actual pivot displacement together with
the remaining linear coefficients. Its normalization agrees with the
previously defined shearing scale, and its size is controlled by the
matrix displacement.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootShearSize_nonneg {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) (u : ℝ) :
    0 ≤ rootShearSize hij g u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem rootShearingOffDiagonalSize_mul_le {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (u : ℝ) :
    |u| * rootShearingOffDiagonalSize i j g ≤ 2 * (n : ℝ) * rootShearSize hij g u := by
  unfold rootShearingOffDiagonalSize
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _k : Fin n, 2 * rootShearSize hij g u := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k = i ∨ k = j
      · simp only [hk, ite_true, mul_zero]
        linarith [rootShearSize_nonneg hij g u]
      · have hki : k ≠ i := fun h => hk (Or.inl h)
        have hkj : k ≠ j := fun h => hk (Or.inr h)
        have hr : |u| * |g.val j k| ≤ rootShearSize hij g u := by
          simpa [root_conjugation_entry, hkj, abs_mul] using
            entry_sub_le_rootShearSize hij g u i k
        have hc : |u| * |g.val k i| ≤ rootShearSize hij g u := by
          simpa [root_conjugation_entry, hki, abs_mul] using
            entry_sub_le_rootShearSize hij g u k j
        simp only [hk, ite_false, mul_add]
        linarith
    _ = _ := by simp; ring

theorem rootShearing_raw_profile_le_size {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (u : ℝ) :
    max |u * (g.val j j - g.val i i) - u ^ 2 * g.val j i|
      (|u| * rootShearingOffDiagonalSize i j g) ≤ 2 * (n : ℝ) * rootShearSize hij g u := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr (Fin.pos i))
  have hp : |u * (g.val j j - g.val i i) - u ^ 2 * g.val j i| ≤ rootShearSize hij g u := by
    simpa only [← root_conjugation_pivot hij g u] using entry_sub_le_rootShearSize hij g u i j
  apply max_le
  · have hS := rootShearSize_nonneg hij g u
    nlinarith
  · exact rootShearingOffDiagonalSize_mul_le hij g u

theorem rootShearing_normalized_profile_identity {n : ℕ} (i j : Fin n) (g : G n)
    (hk : 0 < rootShearingKappa i j g) :
    max |(g.val j j - g.val i i) / rootShearingKappa i j g|
      (Real.sqrt |g.val j i / (rootShearingKappa i j g) ^ 2| +
        rootShearingOffDiagonalSize i j g / rootShearingKappa i j g) = 1 := by
  rw [abs_div, abs_of_pos hk, abs_div, abs_pow, abs_of_pos hk,
    Real.sqrt_div (abs_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos hk,
    ← add_div, max_div_div_right hk.le]
  exact div_self hk.ne'

theorem rootShearing_normalized_profile_le_size {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hk : 0 < rootShearingKappa i j g) (u : ℝ) :
    max |((g.val j j - g.val i i) / rootShearingKappa i j g) *
        (rootShearingKappa i j g * u) -
        (g.val j i / (rootShearingKappa i j g) ^ 2) * (rootShearingKappa i j g * u) ^ 2|
      (|rootShearingKappa i j g * u| *
        (rootShearingOffDiagonalSize i j g / rootShearingKappa i j g)) ≤
      2 * (n : ℝ) * rootShearSize hij g u := by
  have hp : ((g.val j j - g.val i i) / rootShearingKappa i j g) *
      (rootShearingKappa i j g * u) -
      (g.val j i / (rootShearingKappa i j g) ^ 2) * (rootShearingKappa i j g * u) ^ 2 =
      u * (g.val j j - g.val i i) - u ^ 2 * g.val j i := by
    field_simp [hk.ne']
  have hL : |rootShearingKappa i j g * u| *
      (rootShearingOffDiagonalSize i j g / rootShearingKappa i j g) =
      |u| * rootShearingOffDiagonalSize i j g := by
    rw [abs_mul, abs_of_pos hk]
    field_simp [hk.ne']
  rw [hp, hL]
  exact rootShearing_raw_profile_le_size hij g u

end DukePrimeDegree

end

end OAI
