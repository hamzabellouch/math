import OAI.Probability.MatroidSecretary.Selection.AssignedSafe

namespace OAI

/-!
# The exact density-averaged safety loss

This retains the first, sharper inequality in `eq:averaged-safe-count`
(`sections/transfer.tex`, line 330). The density mask is averaged only after
the exact conditional loss has been bounded by `|D ∩ U_i| / κ`. The previous
endpoint route weakened this to `|U_i| / κ` before averaging, which suffices
there but does not state the displayed `|U_i| / (4κ)` estimate.

The statistic remains zero on unlisted outcomes. No conditioning on listing,
focal density bits, or an arrival order is introduced.
-/

namespace MatroidProphet.MainAlgorithm

open Finset

variable {n : ℕ}

/-- Literal first inequality of `eq:averaged-safe-count`, for a fixed true
group and any independent comparison subset of that group. -/
theorem listedSafeStatistic_averaged_exact
    (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n)))
    (hI : M.Indep Y) (q : Fin n → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) :
    retainedFraction * Y.ncard - (trueGroup M d s i).card / (4 * (κ : ℝ)) ≤
      tripleMaskExpectation (fun _ => (1 : ℝ) / 4) q q univ (fun D C T =>
        fairParityExpectation (fun p =>
          (listedSafeStatistic M hE κ (withMasks d D C T) s i Y
            (boolParity p) : ℝ))) := by
  classical
  have hfixed (D : Finset (Fin n)) :
      exitThreshold / 4 * ((D : Set (Fin n)) ∩ Y).ncard -
          (D ∩ trueGroup M d s i).card / (κ : ℝ) ≤
        bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
          fairParityExpectation (fun p =>
            (listedSafeStatistic M hE κ (withMasks d D C T) s i Y
              (boolParity p) : ℝ)))) :=
    listedSafeStatistic_exact_density M hE κ hκ (withMasks d D ∅ ∅)
      s i Y hY hI q hq0 hq1
  have hmean := bitsExpectation_mono (fun _ : Fin n => (1 : ℝ) / 4)
    (by intro e; norm_num) (by intro e; norm_num) univ (fun D _ => hfixed D)
  have hcardY : bitsExpectation (fun _ : Fin n => (1 : ℝ) / 4) univ
      (fun D => (((D : Set (Fin n)) ∩ Y).ncard : ℝ)) = Y.ncard / 4 := by
    have hset (D : Finset (Fin n)) : (D : Set (Fin n)) ∩ Y =
        ((Y.toFinset ∩ D : Finset (Fin n)) : Set (Fin n)) := by
      ext e
      simp only [Set.mem_inter_iff, Finset.mem_coe, mem_inter, Set.mem_toFinset]
      exact and_comm
    simp only [hset, Set.ncard_coe_finset]
    rw [bitsExpectation_card_inter (fun _ : Fin n => (1 : ℝ) / 4)
      univ Y.toFinset (subset_univ _)]
    simp only [sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card']
    ring
  have hcardU : bitsExpectation (fun _ : Fin n => (1 : ℝ) / 4) univ
      (fun D => ((D ∩ trueGroup M d s i).card : ℝ)) =
        (trueGroup M d s i).card / 4 := by
    simpa [Finset.inter_comm, div_eq_mul_inv] using
      bitsExpectation_card_inter (fun _ : Fin n => (1 : ℝ) / 4)
        univ (trueGroup M d s i) (subset_univ _)
  have heq : bitsExpectation (fun _ : Fin n => (1 : ℝ) / 4) univ
      (fun D => exitThreshold / 4 * ((D : Set (Fin n)) ∩ Y).ncard -
        (D ∩ trueGroup M d s i).card / (κ : ℝ)) =
      retainedFraction * Y.ncard - (trueGroup M d s i).card / (4 * (κ : ℝ)) := by
    calc
      _ = bitsExpectation (fun _ : Fin n => (1 : ℝ) / 4) univ
          (fun D => exitThreshold / 4 * ((D : Set (Fin n)) ∩ Y).ncard +
            (-(κ : ℝ)⁻¹) * (D ∩ trueGroup M d s i).card) := by
        apply bitsExpectation_congr
        intro D _
        ring
      _ = exitThreshold / 4 * (Y.ncard / 4) +
          (-(κ : ℝ)⁻¹) * ((trueGroup M d s i).card / 4) := by
        rw [bitsExpectation_add, bitsExpectation_mul_const,
          bitsExpectation_mul_const, hcardY, hcardU]
      _ = _ := by
        norm_num [exitThreshold, retainedFraction]
        ring
  rw [heq] at hmean
  exact hmean

/-- Source specialization for its global independent comparison set `Y`.
The intersection appearing here is exactly the source's `Y_i`; all statistics
are those of the actual density-dependent listed groups. -/
theorem averaged_safe_sampled_labels
    (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hI : M.Indep Y) :
    retainedFraction * (Y ∩ (trueGroup M d s i : Set (Fin n))).ncard -
        (trueGroup M d s i).card / (4 * densityThreshold) ≤
      tripleMaskExpectation (fun _ => (1 : ℝ) / 4)
        (fun _ => thinningRate) (fun _ => thinningRate) univ (fun D C T =>
          fairParityExpectation (fun p =>
            (listedSafeStatistic M hE (2 ^ 100) (withMasks d D C T) s i Y
              (boolParity p) : ℝ))) := by
  have hs := listedSafeStatistic_averaged_exact M hE (2 ^ 100) (by positivity)
    d s i (Y ∩ (trueGroup M d s i : Set (Fin n))) Set.inter_subset_right
    (hI.subset Set.inter_subset_left) (fun _ => thinningRate)
    (fun _ => constants_positive.2.2.1.le)
    (fun _ => by norm_num [thinningRate])
  have heq (D C T : Finset (Fin n)) (p : Bool) :
      listedSafeStatistic M hE (2 ^ 100) (withMasks d D C T) s i
        (Y ∩ (trueGroup M d s i : Set (Fin n))) (boolParity p) =
      listedSafeStatistic M hE (2 ^ 100) (withMasks d D C T) s i Y
        (boolParity p) := by
    simpa only [trueGroup_withMasks] using
      listedSafeStatistic_inter_trueGroup M hE (2 ^ 100)
        (withMasks d D C T) s i Y (boolParity p)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, densityThreshold, heq] using hs

end MatroidProphet.MainAlgorithm

end OAI
