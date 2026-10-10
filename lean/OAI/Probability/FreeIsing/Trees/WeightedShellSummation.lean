import OAI.Probability.FreeIsing.Trees.SubcriticalPathSums
import OAI.Probability.FreeIsing.Trees.WeightedPathSummation

namespace OAI

noncomputable section
namespace Problem367

theorem regularPathWeight_le_closed_threshold {d : ℕ} {theta : ℝ}
    (hcrit : ((d - 1 : ℕ) : ℝ) * theta ^ 2 ≤ 1) (n : ℕ) :
    regularPathWeight d theta n ≤ (d : ℝ) * theta ^ 2 := by
  rw [regularPathWeight_eq]
  exact mul_le_of_le_one_right (by positivity)
    (pow_le_one₀ (by positivity) hcrit)

theorem summable_and_tsum_shell_le_path {d : ℕ} {theta : ℝ}
    (hcrit : ((d - 1 : ℕ) : ℝ) * theta ^ 2 ≤ 1)
    {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n) (hf : Summable f) :
    Summable (fun n => regularPathWeight d theta n * f (n + 1)) ∧
    (∑' n, regularPathWeight d theta n * f (n + 1)) ≤
      ((d : ℝ) * theta ^ 2) * (∑' n, f n) := by
  have hW : 0 ≤ (d : ℝ) * theta ^ 2 := by positivity
  have hshift : Summable (fun n => f (n + 1)) := (summable_nat_add_iff 1).mpr hf
  have hbound (n : ℕ) : regularPathWeight d theta n * f (n + 1) ≤
      ((d : ℝ) * theta ^ 2) * f (n + 1) :=
    mul_le_mul_of_nonneg_right (regularPathWeight_le_closed_threshold hcrit n) (hf0 _)
  have hs : Summable (fun n => regularPathWeight d theta n * f (n + 1)) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (regularPathWeight_nonneg d theta n) (hf0 _))
      hbound (hshift.mul_left _)
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n, ((d : ℝ) * theta ^ 2) * f (n + 1) :=
      hs.tsum_le_tsum hbound (hshift.mul_left _)
    _ = ((d : ℝ) * theta ^ 2) * (∑' n, f (n + 1)) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (tsum_comp_le_tsum_of_inj (i := fun n : ℕ => n + 1) hf hf0
        (fun _ _ h => Nat.add_right_cancel h)) hW

theorem shell_noise_drift_le_path_sums {d : ℕ} {theta V : ℝ}
    (hcrit : ((d - 1 : ℕ) : ℝ) * theta ^ 2 ≤ 1) (hV : 0 ≤ V)
    {Q L : ℕ → ℝ} (hQ0 : ∀ n, 0 ≤ Q n) (hL0 : ∀ n, 0 ≤ L n)
    (hQ : Summable Q) (hL : Summable L) (hZ : Summable (fun n => Real.sqrt (Q n))) :
    2 * V + (∑' n, regularPathWeight d theta n *
      (Q (n + 1) + 2 * L (n + 1) + 4 * Real.sqrt (2 * V) * Real.sqrt (Q (n + 1)))) ≤
    (2 + 8 * ((d : ℝ) * theta ^ 2)) *
      (V + (∑' n, Q n) + (∑' n, L n) + Real.sqrt V * (∑' n, Real.sqrt (Q n))) := by
  obtain ⟨hsQ, hbQ⟩ := summable_and_tsum_shell_le_path hcrit hQ0 hQ
  obtain ⟨hsL, hbL⟩ := summable_and_tsum_shell_le_path hcrit hL0 hL
  obtain ⟨hsZ, hbZ⟩ := summable_and_tsum_shell_le_path hcrit (fun _ => Real.sqrt_nonneg _) hZ
  have heq : (∑' n, regularPathWeight d theta n *
      (Q (n + 1) + 2 * L (n + 1) + 4 * Real.sqrt (2 * V) * Real.sqrt (Q (n + 1)))) =
      (∑' n, regularPathWeight d theta n * Q (n + 1)) +
      2 * (∑' n, regularPathWeight d theta n * L (n + 1)) +
      4 * Real.sqrt (2 * V) * (∑' n, regularPathWeight d theta n * Real.sqrt (Q (n + 1))) := by
    calc
      _ = ∑' n, ((regularPathWeight d theta n * Q (n + 1)) +
          2 * (regularPathWeight d theta n * L (n + 1)) +
          (4 * Real.sqrt (2 * V)) * (regularPathWeight d theta n * Real.sqrt (Q (n + 1)))) := by
        apply tsum_congr
        intro n
        ring
      _ = _ := by
        rw [(hsQ.add (hsL.mul_left 2)).tsum_add (hsZ.mul_left _),
          hsQ.tsum_add (hsL.mul_left 2), tsum_mul_left, tsum_mul_left]
  rw [heq]
  have hQr : 0 ≤ ∑' n, Q n := tsum_nonneg hQ0
  have hLr : 0 ≤ ∑' n, L n := tsum_nonneg hL0
  have hZr : 0 ≤ ∑' n, Real.sqrt (Q n) := tsum_nonneg (fun _ => Real.sqrt_nonneg _)
  have hW : 0 ≤ (d : ℝ) * theta ^ 2 := by positivity
  have hroot : Real.sqrt (2 * V) ≤ 2 * Real.sqrt V := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hV]
  have hZbound := mul_le_mul_of_nonneg_left hbZ (by positivity : 0 ≤ 4 * Real.sqrt (2 * V))
  have hZbound' : 4 * Real.sqrt (2 * V) * ((d : ℝ) * theta ^ 2 * (∑' n, Real.sqrt (Q n))) ≤
      8 * ((d : ℝ) * theta ^ 2) * (Real.sqrt V * (∑' n, Real.sqrt (Q n))) := by
    nlinarith [mul_le_mul_of_nonneg_right hroot (mul_nonneg hW hZr)]
  have hLbound := mul_le_mul_of_nonneg_left hbL (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [mul_nonneg hW hV, mul_nonneg hW hQr, mul_nonneg hW hLr,
    mul_nonneg (Real.sqrt_nonneg V) hZr]

end Problem367

end

end OAI
