import OAI.NumberTheory.Ostmann.Construction.SelectedProductBudget
import OAI.NumberTheory.Ostmann.Arithmetic.MovingProductRigidity

namespace OAI

/-! # The selected finite compensation list gives a valid full cutoff schedule -/
namespace Ostmann
open scoped BigOperators

theorem movingProductExponent_gap_of_constant_tail (T : ℕ → ℝ) (W t : ℝ) (k : ℕ)
    (hbefore : ∀ n < k, 2 * T n ≤ movingProductExponent T W n)
    (htail : ∀ n, k ≤ n → T n = t)
    (hbase : 2 * t ≤ movingProductExponent T W k) :
    ∀ n, 2 * T n ≤ movingProductExponent T W n := by
  have hb : ∀ n, k ≤ n → 2 * t ≤ movingProductExponent T W n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hbase
    | succ n hn ih =>
      rw [movingProductExponent, htail n hn]
      linarith
  intro n
  by_cases hn : n < k
  · exact hbefore n hn
  · rw [htail n (by omega)]
    exact hb n (by omega)

theorem selectedCompensation_pivot_tail (centers : List ℕ) (G : ℝ) (n : ℕ)
    (hn : centers.length ≤ n) :
    movingCellPivotExponent (fun _ => G) (selectedCompensationCenter centers) n = G - 1 := by
  simp [movingCellPivotExponent, selectedCompensationCenter, List.drop_eq_nil_of_le hn]

theorem selectedCompensation_pivot_nonneg (centers : List ℕ) (G : ℝ) (hG : 1 ≤ G)
    (n : ℕ) :
    0 ≤ movingCellPivotExponent (fun _ => G) (selectedCompensationCenter centers) n := by
  simp only [movingCellPivotExponent, selectedCompensationCenter, add_sub_cancel_right]
  positivity

/-- Every finite selected pivot gap is positive, and the unused constant tail
preserves that inequality. Hence the constructed frequencies are monotone on
all natural indices, as required by the original sampled-history recursion. -/
theorem selectedCompensation_product_gaps
    {A B : Set ℕ} {N hi : ℕ} {a C L X G J W E : ℝ} {D : Finset ℕ}
    {centers : List ℕ} (k : ℕ) (BD Bz : ℝ)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) centers
      (movingCompensationTargets J (movingCompensationGaps k BD Bz L)))
    (hW : |W - (2 * G + J +
      (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum)| ≤ E)
    (hbudget : E + k * (256 * tailDefectBudget a C X + 9) ≤
      (spectatorBulkCount k L : ℝ))
    (hD : 0 ≤ tailDefectBudget a C X)
    (hR : 256 * tailDefectBudget a C X + 9 ≤ (spectatorBulkCount k L : ℝ) / 40)
    (hJ : (spectatorBulkCount k L : ℝ) ≤ J)
    (hk : 1 ≤ k) (hBD : 2 ≤ BD) (hBz : 0 ≤ Bz) :
    ∀ n, 2 * movingCellPivotExponent (fun _ => G) (selectedCompensationCenter centers) n ≤
      movingProductExponent
        (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter centers)) W n := by
  let m : ℝ := spectatorBulkCount k L
  let R := 256 * tailDefectBudget a C X + 9
  let ws := movingCompensationTargets J (movingCompensationGaps k BD Bz L)
  let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter centers)
  let U := movingTargetPivotExponent G ws
  let Z := 2 * G + J + ws.sum
  have hlen : centers.length = k := by
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using
      hcenters.length_eq
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hTU (n : ℕ) (hn : n < k) : |T n - U n| ≤ (2 : ℝ) ^ n * R := by
    exact selectedCompensation_pivot_error hcenters n (by simpa [ws] using hn) G
  have hround (n : ℕ) (hn : n ≤ k) :
      |movingProductExponent T W n - movingProductExponent U Z n| ≤ (2 : ℝ) ^ n * m := by
    have hh := movingProductExponent_rounding_abs T U W Z E R n hW
      (fun j hj => hTU j (hj.trans_le hn))
    have hnk : (n : ℝ) ≤ k := by exact_mod_cast hn
    have he : E + n * R ≤ m := by
      have hh := mul_le_mul_of_nonneg_right hnk hR0
      linarith
    exact hh.trans (mul_le_mul_of_nonneg_left he (by positivity))
  apply movingProductExponent_gap_of_constant_tail T W (G - 1) k
  · intro n hn
    have he := (abs_le.mp (hround n hn.le)).1
    have ht := (abs_le.mp (hTU n hn)).2
    have hg := movingProductExponent_target_gap G J (movingCompensationGaps k BD Bz L) n
      (by simpa using hn)
    change movingProductExponent U Z n - 2 * U n = _ at hg
    have hd : 2 * m ≤ ((movingCompensationGaps k BD Bz L).drop n).headD 0 := by
      have hnmem : ((movingCompensationGaps k BD Bz L).drop n).headD 0 ∈
          movingCompensationGaps k BD Bz L := by
        have hne : (movingCompensationGaps k BD Bz L).drop n ≠ [] := by
          intro hnil
          have hh := congrArg List.length hnil
          simp only [List.length_drop, movingCompensationGaps_length, List.length_nil] at hh
          omega
        rcases he : (movingCompensationGaps k BD Bz L).drop n with _ | ⟨d, ds⟩
        · exact False.elim (hne he)
        · simp only [List.headD_cons]
          exact List.mem_of_mem_drop (a := d) (i := n) (by rw [he]; simp)
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hnmem
      rw [← hi]
      have hr : (0 : ℝ) < 2 ^ (i : ℕ) := by positivity
      have hz : 0 ≤ Real.log ((k : ℝ) ^ 4) := Real.log_nonneg (one_le_pow₀ (by exact_mod_cast hk))
      have hp : 0 ≤ Real.log ((2 : ℝ) ^ (i : ℕ)) :=
        Real.log_nonneg (one_le_pow₀ (by norm_num))
      dsimp only [spectatorStepGap]
      have hcoeff : 2 ≤ BD + Bz * Real.log ((k : ℝ) ^ 4) +
          (2 / 5 : ℝ) * Real.log ((2 : ℝ) ^ (i : ℕ)) := by
        have ht : 0 ≤ Bz * Real.log ((k : ℝ) ^ 4) := mul_nonneg hBz hz
        linarith
      have hmul := mul_le_mul_of_nonneg_right hcoeff hm0
      dsimp only [m] at *
      rw [mul_assoc, mul_div_cancel_left₀ _ hr.ne']
      exact hmul
    have hgap := mul_le_mul_of_nonneg_left hd (show 0 ≤ (2 : ℝ) ^ n by positivity)
    have hsmall := mul_le_mul_of_nonneg_left hR (show 0 ≤ (2 : ℝ) ^ n by positivity)
    change 2 * T n ≤ movingProductExponent T W n
    dsimp only [R, m] at *
    nlinarith only [he, ht, hg, hgap, hsmall, mul_nonneg (show 0 ≤ (2 : ℝ) ^ n by positivity) hm0]
  · intro n hn
    exact selectedCompensation_pivot_tail centers G n (by omega)
  · have he := (abs_le.mp (hround k le_rfl)).1
    have hdrop : ws.drop k = [] := by simp [ws]
    have hu := movingProductExponent_targets G J ws k
    rw [hdrop] at hu
    simp only [List.sum_nil, add_zero] at hu
    change movingProductExponent U Z k = _ at hu
    have hj := mul_le_mul_of_nonneg_left hJ (show 0 ≤ (2 : ℝ) ^ k by positivity)
    dsimp only [m] at he hj
    change 2 * (G - 1) ≤ movingProductExponent T W k
    linarith

end Ostmann

end OAI
