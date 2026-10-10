import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingLogTime
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingCoefficientBounds

namespace OAI

/-!
# Uniform control during the logarithmic recurrence window

The shearing scale remains small throughout the chosen diagonal window.
The growing matrix entries are bounded by that scale; all other
off-diagonal entries contract. Thus moving to the selected recurrence
time preserves convergence of the relative return matrices to identity.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootShearingKappa_window_bound
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n)
    (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g)
    (hsmall : rootShearingKappa i j g ≤ 1)
    (τ : ℝ) (hτ : τ ∈ Icc 0 (rootShearingLogTime i j g)) :
    rootShearingKappa i j (rootPairConjugate i j τ g) ≤
      Real.exp (-3 * rootShearingLogTime i j g) := by
  let T := rootShearingLogTime i j g
  have hT : 0 ≤ T := rootShearingLogTime_nonneg hij g hnot hsmall
  have hk := rootShearingLogTime_normalizes hij g hnot
  have hA := rootShearingKappa_diagonal_bound i j g
  have hU : rootShearingMovingSize i j g ≤ rootShearingKappa i j g := le_max_right _ _
  rw [rootShearingKappa_conjugate hij]
  apply max_le
  · apply hA.trans
    rw [hk]
    exact Real.exp_le_exp.mpr (by dsimp only [T] at hT ⊢; linarith)
  · calc
      Real.exp τ * rootShearingMovingSize i j g ≤
          Real.exp T * rootShearingKappa i j g :=
        mul_le_mul (Real.exp_le_exp.mpr hτ.2) hU
          (rootShearingMovingSize_nonneg i j g) (Real.exp_pos _).le
      _ = Real.exp (-3 * rootShearingLogTime i j g) := by
        rw [hk, ← Real.exp_add]
        congr 1
        dsimp only [T]
        ring

theorem rootPairConjugate_entry_difference_bound
    {n : ℕ} {i j : Fin n} (g : G n)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hsmall : rootShearingKappa i j (rootPairConjugate i j τ g) ≤ 1)
    (r s : Fin n) :
    |(rootPairConjugate i j τ g).val r s - (1 : G n).val r s| ≤
      |g.val r s - (1 : G n).val r s| +
        rootShearingKappa i j (rootPairConjugate i j τ g) := by
  have hk := rootShearingKappa_nonneg i j (rootPairConjugate i j τ g)
  by_cases hrs : r = s
  · subst s
    rw [rootPairConjugate_diagonal]
    linarith
  have hzero : (1 : G n).val r s = 0 := by
    simp [Matrix.SpecialLinearGroup.coe_one, hrs]
  rw [hzero, sub_zero, sub_zero]
  by_cases hrj : r = j
  · subst r
    have hb := rootShearingKappa_row_bound (rootPairConjugate i j τ g) (Ne.symm hrs) hsmall
    linarith [abs_nonneg (g.val j s)]
  by_cases hsi : s = i
  · subst s
    have hb := rootShearingKappa_col_bound (rootPairConjugate i j τ g) hrs hsmall
    linarith [abs_nonneg (g.val r i)]
  have hwr : rootPairWeights i j r ≤ 0 := by
    simp only [rootPairWeights, hrj, ite_false, zero_sub]
    split_ifs <;> norm_num
  have hws : 0 ≤ rootPairWeights i j s := by
    simp only [rootPairWeights, hsi, ite_false, sub_zero]
    split_ifs <;> norm_num
  have he : Real.exp ((rootPairWeights i j r - rootPairWeights i j s) * τ) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hτ)
  have hentry : (rootPairConjugate i j τ g).val r s =
      Real.exp ((rootPairWeights i j r - rootPairWeights i j s) * τ) * g.val r s := by
    simp only [rootPairConjugate, rootPairFlow, conjugation_entry]
  rw [hentry, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans (by linarith)

end DukePrimeDegree

end

end OAI
