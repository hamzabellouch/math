import OAI.Geometry.NodalSets.Elliptic.CommonLocalExtension
import OAI.Geometry.NodalSets.Elliptic.RealInteriorJetEstimate

namespace OAI

namespace Yau.Geometry
open Metric
open scoped ContDiff
noncomputable section

def realCutoffRadius (r R : ℝ) (n : ℕ) : ℝ := r+(R-r)/(2:ℝ)^n

lemma realCutoffRadius_gt (r R : ℝ) (hR : r < R) (n : ℕ) :
    r < realCutoffRadius r R n := by
  have h := div_pos (sub_pos.mpr hR) (pow_pos (by norm_num : (0:ℝ)<2) n)
  dsimp [realCutoffRadius]; linarith

lemma realCutoffRadius_succ_lt (r R : ℝ) (hR : r < R) (n : ℕ) :
    realCutoffRadius r R (n+1) < realCutoffRadius r R n := by
  have h := div_pos (sub_pos.mpr hR) (pow_pos (by norm_num : (0:ℝ)<2) n)
  dsimp [realCutoffRadius]
  rw [pow_succ,div_mul_eq_div_div]
  linarith

lemma realCutoffRadius_le (r R : ℝ) (hR : r < R) (n : ℕ) :
    realCutoffRadius r R n ≤ R := by
  have h : (R-r)/(2:ℝ)^n ≤ R-r :=
    div_le_self (sub_nonneg.mpr hR.le) (one_le_pow₀ (by norm_num))
  dsimp [realCutoffRadius]; linarith

def realBallCutoff (y : Yau.Jets.Coord) (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (n : ℕ) : ContDiffBump y :=
  ⟨realCutoffRadius r R (n+1),realCutoffRadius r R n,
    hr.trans (realCutoffRadius_gt r R hR _),realCutoffRadius_succ_lt r R hR n⟩

theorem real_ball_cutoff_chain (y : Yau.Jets.Coord) (r R : ℝ) (hr : 0 < r) (hR : r < R) :
    ∃ eta : ℕ → Yau.Jets.Coord → ℝ,
      (∀ j, ContDiff ℝ ∞ (eta j)) ∧ (∀ j, HasCompactSupport (eta j)) ∧
      (∀ j x, 0 ≤ eta j x ∧ eta j x ≤ 1) ∧
      (∀ j, tsupport (eta j) ⊆ closedBall y R) ∧
      (∀ j x, x ∈ closedBall y r → eta j x=1) ∧
      (∀ j x, x ∈ tsupport (eta (j+1)) → eta j x=1) := by
  refine ⟨fun j ↦ realBallCutoff y r R hr hR j,?_,?_,?_,?_,?_,?_⟩
  · intro j; exact (realBallCutoff y r R hr hR j).contDiff
  · intro j; exact (realBallCutoff y r R hr hR j).hasCompactSupport
  · intro j x
    exact ⟨(realBallCutoff y r R hr hR j).nonneg,(realBallCutoff y r R hr hR j).le_one⟩
  · intro j
    rw [(realBallCutoff y r R hr hR j).tsupport_eq]
    exact closedBall_subset_closedBall (realCutoffRadius_le r R hR j)
  · intro j x hx
    apply (realBallCutoff y r R hr hR j).one_of_mem_closedBall
    exact closedBall_subset_closedBall (realCutoffRadius_gt r R hR (j+1)).le hx
  · intro j x hx
    apply (realBallCutoff y r R hr hR j).one_of_mem_closedBall
    rw [(realBallCutoff y r R hr hR (j+1)).tsupport_eq] at hx
    exact hx

end
end Yau.Geometry

end OAI
