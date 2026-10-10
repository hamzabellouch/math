import OAI.Probability.SATComputability.ActualFreeMoment
import OAI.Probability.SATComputability.ExchangeableBlocks
import OAI.Probability.SATComputability.DeletionMean

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped NNReal Classical

noncomputable def uniformFreeConstant : ℝ := deletionMomentConstant + 400

theorem uniformFreeConstant_nonneg : 0 ≤ uniformFreeConstant := by
  unfold uniformFreeConstant
  linarith [deletionMomentConstant_nonneg]

theorem free_gap_power_le {n M r : ℕ} (v : Fin n)
    (xs : Fin M → Finset (DeletionCandidate n)) :
    (maskLifetime M (freeDeletionBudgetMask n r v) xs -
      maskLifetime M (deletionBudgetMask n r) xs)^(6/5 : ℝ) ≤ (M : ℝ)^(6/5 : ℝ) := by
  apply Real.rpow_le_rpow
  · exact sub_nonneg.mpr (maskLifetime_mono (deletionBudgetMask_subset_free n r v) xs)
  · exact (sub_le_self _ (maskLifetime_nonneg _ xs)).trans (maskLifetime_le _ xs)
  · norm_num

theorem actual_free_deletion_moment (n r : ℕ) [NeZero n] (v : Fin n) :
    (FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ)).expect
      (fun xs => (maskLifetime (20*n) (freeDeletionBudgetMask n r v) xs -
        maskLifetime (20*n) (deletionBudgetMask n r) xs)^(6/5 : ℝ)) ≤ uniformFreeConstant := by
  cases n with
  | zero => exact Fin.elim0 v
  | succ n =>
    cases n with
    | zero =>
      have h := (FiniteLaw.pi (fun _ : Fin (20*1) =>
        candidateBlock (n := 1) 1 3 Finset.univ)).expect_mono
          (fun xs => free_gap_power_le v xs (r := r))
      rw [FiniteLaw.expect_const] at h
      apply h.trans
      have hp : (20 : ℝ)^(6/5 : ℝ) ≤ 20^2 := by
        simpa only [Real.rpow_natCast] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 20)
            (by norm_num : (6/5 : ℝ) ≤ (2 : ℕ))
      norm_num only [Nat.mul_one, Nat.cast_ofNat] at *
      unfold uniformFreeConstant
      linarith [deletionMomentConstant_nonneg]
    | succ n =>
      let e : Equiv.Perm (Fin (n+1+1)) := Equiv.swap 0 v
      have hv : e 0 = v := Equiv.swap_apply_left _ _
      let φ := fun xs : Fin (20*(n+1+1)) → Finset (DeletionCandidate (n+1+1)) =>
        (maskLifetime (20*(n+1+1)) (freeDeletionBudgetMask (n+1+1) r v) xs -
          maskLifetime (20*(n+1+1)) (deletionBudgetMask (n+1+1) r) xs)^(6/5 : ℝ)
      have he := candidatePath_permutation (20*(n+1+1)) 3 e 1 φ
      have hφ (xs) : φ (fun j => renameMask e (xs j)) =
          freeGap (n+1) (20*(n+1+1)) r xs := by
        dsimp only [φ, freeGap]
        rw [maskLifetime_permutation e (freeDeletionBudgetMask (n+1+1) r 0)
          (freeDeletionBudgetMask (n+1+1) r v) xs (fun x => by
            simpa only [hv] using freeDeletionBudget_permutation e 0 x),
          maskLifetime_permutation e (deletionBudgetMask (n+1+1) r)
            (deletionBudgetMask (n+1+1) r) xs (deletionBudget_permutation e)]
      simp only [hφ] at he
      rw [← he]
      exact (actual_free_deletion_moment_zero r).trans
        (by unfold uniformFreeConstant; linarith)

theorem actual_deletion_mean (n r : ℕ) [NeZero n] :
    let P := FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ)
    P.expect (maskLifetime (20*n) (deletionBudgetMask n r)) -
      P.expect (maskLifetime (20*n) (deletionBudgetMask n 0)) ≤
      6*((n : ℝ)*uniformFreeConstant)^(5/6 : ℝ)*(r : ℝ)^(1/6 : ℝ) := by
  dsimp only
  have h := finite_deletion_mean (r := r)
    (FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ))
    (fun xs => fixedMaskDeletionTime xs) (fun xs => fixedMaskDeletionTime_mono xs)
    uniformFreeConstant_nonneg
    (fun j _ v => by
      simpa only [freeMaskDeletionTime_eq, bestMaskDeletionTime_eq] using
        actual_free_deletion_moment n j v)
  simpa only [bestMaskDeletionTime_eq] using h

end FixedClauseThreshold.Computability

end OAI
