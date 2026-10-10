import OAI.NumberTheory.JointDickman.Amplification.RampedCandidate

namespace OAI

/-! # The moving block origin is a bounded, slowly varying parameter -/
namespace JointDickman
open Finset Classical

noncomputable def countingOriginParameter (T N u : ℕ) : ℝ :=
  min 3 ((u : ℝ)/((T : ℝ)*(N+1)))

theorem countingOriginParameter_bound (T N u : ℕ) :
    |countingOriginParameter T N u| ≤ 3 := by
  rw [abs_of_nonneg (le_min (by norm_num) (by positivity))]
  exact min_le_left _ _

theorem countingOriginParameter_step {T : ℕ} (hT : 0 < T) (N q b r : ℕ) (hr : r < q) :
    |countingOriginParameter T N (b*q+r)-countingOriginParameter T N (b*q)| ≤
      (q : ℝ)/((T : ℝ)*(N+1)) := by
  have hd : (0 : ℝ) < (T : ℝ)*(N+1) := by positivity
  have hh := abs_min_sub_min_le_max (3 : ℝ) (((b*q+r : ℕ) : ℝ)/((T : ℝ)*(N+1)))
    3 (((b*q : ℕ) : ℝ)/((T : ℝ)*(N+1)))
  have habs : (0 : ℝ) ≤ |((b*q+r : ℕ) : ℝ)/((T : ℝ)*(N+1))-((b*q : ℕ) : ℝ)/((T : ℝ)*(N+1))| := abs_nonneg _
  simp only [sub_self,abs_zero,max_eq_right habs] at hh
  apply hh.trans
  have he : ((b*q+r : ℕ) : ℝ)/((T : ℝ)*(N+1))-((b*q : ℕ) : ℝ)/((T : ℝ)*(N+1)) =
      (r : ℝ)/((T : ℝ)*(N+1)) := by push_cast; ring
  rw [he,abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hr.le) hd.le

theorem rampedCandidateCutoff_originParameter {M T : ℕ} {w : ℝ} (_hT : 0 < T)
    (hw : 0 < w) (B N u : ℕ) (e : BlockCandidateIndex M) :
    rampedCandidateCutoff B T w (countingOriginParameter T N u) e =
      rampedCandidateCutoff B T w ((u : ℝ)/((T : ℝ)*(N+1))) e := by
  let s := (u : ℝ)/((T : ℝ)*(N+1))
  by_cases hs : s ≤ 3
  · change rampedCandidateCutoff B T w (min 3 s) e = rampedCandidateCutoff B T w s e
    rw [min_eq_right hs]
  · have hs3 : 3 < s := lt_of_not_ge hs
    change candidateCutoff _ _ e * _ = candidateCutoff _ _ e * _
    by_cases he : amplificationBump ((candidateLow e : ℝ)/(T*candidateQuotient e)) = 0
    · simp [candidateCutoff,amplificationInnerWeight,he]
    · have hx : (candidateLow e : ℝ)/(T*candidateQuotient e) ≤ 2 := by
        by_contra hn
        apply he
        exact amplificationBump_zero (Or.inr (le_of_lt (lt_of_not_ge hn)))
      have hmin : countingOriginParameter T N u = 3 := min_eq_left hs3.le
      rw [hmin,countingRamp_zero hw (by linarith),countingRamp_zero hw (by linarith)]

end JointDickman

end OAI
