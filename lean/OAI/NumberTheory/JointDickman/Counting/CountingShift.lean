import OAI.NumberTheory.JointDickman.Counting.CountingCutoffError

namespace OAI

/-! # Moving a counting threshold from an endpoint to its block origin -/
namespace JointDickman

 theorem countingRamp_translate (δ s x : ℝ) :
    countingRamp δ s x = averagingRamp 0 δ (x-s) := by
  have he : min (s+δ) (max s x)-s = min δ (max 0 (x-s)) := by
    rw [← min_sub_sub_right,← max_sub_sub_right]
    simp
  unfold countingRamp averagingRamp
  rw [he]
  simp

theorem countingRamp_threshold_lipschitz {δ : ℝ} (hδ : 0 < δ) (s t x : ℝ) :
    |countingRamp δ s x-countingRamp δ t x| ≤ |s-t|/δ := by
  rw [countingRamp_translate,countingRamp_translate]
  have he := (averagingRamp_lipschitz (a := 0) hδ).dist_le_mul (x-s) (x-t)
  simp only [Real.dist_eq] at he
  change |averagingRamp 0 δ (x-s)-averagingRamp 0 δ (x-t)| ≤
    (1/(δ-0))*|(x-s)-(x-t)| at he
  simp only [sub_zero] at he
  have hs : (x-s)-(x-t) = -(s-t) := by ring
  simpa only [hs,abs_neg,one_div_mul_eq_div] using he

theorem countingRamp_block_shift {δ : ℝ} (hδ : 0 < δ) {T M : ℕ}
    (hT : 0 < T) (N u : ℕ) (i : Fin M) (x : ℝ) :
    |countingRamp δ (((u+(i.val+1) : ℕ) : ℝ)/((T : ℝ)*(N+1))) x-
      countingRamp δ ((u : ℝ)/((T : ℝ)*(N+1))) x| ≤
      (M : ℝ)/((T : ℝ)*(N+1)*δ) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hd : (0 : ℝ) < (T : ℝ)*(N+1) := by positivity
  have hi : ((i.val+1 : ℕ) : ℝ) ≤ M := by exact_mod_cast i.isLt
  have he : (((u+(i.val+1) : ℕ) : ℝ)/((T : ℝ)*(N+1)))-
      ((u : ℝ)/((T : ℝ)*(N+1))) = ((i.val+1 : ℕ) : ℝ)/((T : ℝ)*(N+1)) := by
    push_cast
    ring
  apply (countingRamp_threshold_lipschitz hδ _ _ x).trans
  rw [he,abs_of_nonneg (by positivity),div_div]
  exact div_le_div_of_nonneg_right hi (by positivity)

end JointDickman

end OAI
