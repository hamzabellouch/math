import OAI.NumberTheory.Ostmann.Construction.SelectedProductSchedule
import OAI.NumberTheory.Ostmann.Arithmetic.MovingProductInitialCutoff

namespace OAI

/-! # The actual selected list satisfies the cutoff and rigidity hypotheses -/
namespace Ostmann
open scoped BigOperators

theorem selectedCompensation_cutoff_data
    {A B : Set ℕ} {N hi : ℕ} {a C L X G J W Y E : ℝ} {D : Finset ℕ}
    {centers : List ℕ} (k : ℕ) (Bs BD Bz : ℝ)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) centers
      (movingCompensationTargets J (movingCompensationGaps k BD Bz L)))
    (hW : |W - (2 * G + J +
      (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum)| ≤ E)
    (hbase : 2 * G + J +
      (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum - Y =
        spectatorBaseGap Bs ((k : ℝ) ^ 4) (spectatorBulkCount k L))
    (hbudget : ∀ n ≤ k, E + n * (256 * tailDefectBudget a C X + 9) ≤
      (spectatorBulkCount k L : ℝ))
    (hD : 0 ≤ tailDefectBudget a C X)
    (hR : 256 * tailDefectBudget a C X + 9 ≤ (spectatorBulkCount k L : ℝ) / 40)
    (hJ : (spectatorBulkCount k L : ℝ) ≤ J)
    (hG : 1 ≤ G) (hk : 1 ≤ k) (hBs : 2 ≤ Bs)
    (hBD : Bs + 1 ≤ BD) (hBz : 8 ≤ Bz)
    (hm : 256 ≤ (spectatorBulkCount k L : ℝ)) :
    let m := spectatorBulkCount k L
    let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter centers)
    let V := movingProductNaturalCutoff T W Y ((m : ℝ) / 4)
    Monotone V ∧ Y ≤ W ∧
      (∀ n, 0 ≤ movingProductExponent T W n - T n) ∧
      (∀ n ≤ k,
        (V n : ℝ) ≤ Real.exp (movingFrequencyRate Bs BD Bz ((k : ℝ) ^ 4) n * m) ∧
        ((transferFrequencyRange (V n)).card : ℝ) ≤
          Real.exp ((movingFrequencyRate Bs BD Bz ((k : ℝ) ^ 4) n + 1) * m)) ∧
      (∀ n < k, (1 / 10 : ℝ) * (2 : ℝ) ^ n * m ≤
        (movingProductExponent T W n - 2 * T n) -
          movingProductFrequencyExponent T W Y ((m : ℝ) / 4) n) := by
  intro m T V
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hk)
  have hgaps := selectedCompensation_product_gaps k BD Bz hcenters hW
    (hbudget k le_rfl) hD hR hJ hk (by linarith) (by linarith)
  change ∀ n, 2 * T n ≤ movingProductExponent T W n at hgaps
  have hT0 : ∀ n, 0 ≤ T n := selectedCompensation_pivot_nonneg centers G hG
  have hY : Y ≤ W := by
    have herr := (abs_le.mp hW).1
    have he := hbudget 0 (Nat.zero_le k)
    have hzlog := Real.log_nonneg hz
    have hb : (m : ℝ) ≤ spectatorBaseGap Bs ((k : ℝ) ^ 4) m := by
      unfold spectatorBaseGap
      nlinarith only [hBs, hzlog, hm0]
    simp only [Nat.cast_zero, zero_mul, add_zero] at he
    linarith
  refine ⟨movingProductNaturalCutoff_monotone T W Y _ hgaps, hY, ?_, ?_, ?_⟩
  · intro n
    linarith [hgaps n, hT0 n]
  · intro n hn
    have hterr (j : ℕ) (hj : j < n) :=
      selectedCompensation_pivot_error hcenters j
        (by simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using
          hj.trans_le hn) G
    have hrate := movingProductFrequency_prescribed_rate G J Y Bs BD Bz L k n hn T W E
      (256 * tailDefectBudget a C X + 9) hbase hW hterr (hbudget n hn)
      (by linarith) (by linarith) (by linarith) hz (by linarith)
    have hless := movingProductFrequency_mono_mass T W Y ((m : ℝ) / 4) m n (by linarith)
    have hfreq : movingProductFrequencyExponent T W Y ((m : ℝ) / 4) n ≤
        movingFrequencyRate Bs BD Bz ((k : ℝ) ^ 4) n * m := hless.trans hrate
    have hnonneg : 0 ≤ movingProductFrequencyExponent T W Y ((m : ℝ) / 4) n := by
      have hE := movingProductExponent_monotone T W hgaps (Nat.zero_le n)
      change W ≤ movingProductExponent T W n at hE
      unfold movingProductFrequencyExponent
      linarith [mul_nonneg (show 0 ≤ (2 : ℝ) ^ n by positivity)
        (Real.sqrt_nonneg (4 * ((m : ℝ) / 4)))]
    refine ⟨(Nat.floor_le (Real.exp_pos _).le).trans (Real.exp_le_exp.mpr hfreq), ?_⟩
    apply movingProductNaturalCutoff_card_bound T W Y ((m : ℝ) / 4) _ n hnonneg
    have hl : Real.log 3 ≤ 2 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
    nlinarith only [hfreq, hl, hm]
  · intro n hn
    have ht := (abs_le.mp (selectedCompensation_pivot_error hcenters n
      (by simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using hn) G)).2
    have hmargin := movingProductFrequency_prescribed_margin G J Y Bs BD Bz L k n hn T W
      (256 * tailDefectBudget a C X + 9) hbase (by linarith) hR hBD hBz hz (by linarith)
    have hless := movingProductFrequency_mono_mass T W Y ((m : ℝ) / 4) m n (by linarith)
    linarith

end Ostmann

end OAI
