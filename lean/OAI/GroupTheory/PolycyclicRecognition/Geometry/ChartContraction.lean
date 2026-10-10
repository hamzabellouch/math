import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

namespace OAI

/-! # Controlled contraction from locally Lipschitz exponential coordinates

This is the elementary metric bridge in the replacement construction. The
local metric compatibility of a chosen Lie chart is an explicit premise here;
it does not follow from a merely topological exponential chart.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [MetricSpace G] [ProperSpace G] [One G]

def chartContraction (φ : E ≃ₜ G) (s : ℝ) (z : G) : G := φ (s • φ.symm z)

omit [ProperSpace E] [ProperSpace G] in
@[simp] theorem chartContraction_zero (φ : E ≃ₜ G) (hφ : φ 0 = 1) (z : G) :
    chartContraction φ 0 z = 1 := by simp [chartContraction, hφ]

omit [ProperSpace E] [ProperSpace G] [One G] in
@[simp] theorem chartContraction_one (φ : E ≃ₜ G) (z : G) :
    chartContraction φ 1 z = z := by simp [chartContraction]

/-- On a fixed metric ball, radial contraction has a uniform time bound
and a spatial bound proportional to the radial parameter. -/
theorem chartContraction_bounds (φ : E ≃ₜ G) (hφ : φ 0 = 1)
    (hforward : LocallyLipschitz φ) (hbackward : LocallyLipschitz φ.symm)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ∀ z ∈ closedBall (1 : G) R,
        dist (chartContraction φ s z) (chartContraction φ t z) ≤ C * |s - t|) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ closedBall (1 : G) R,
        ∀ w ∈ closedBall (1 : G) R,
        dist (chartContraction φ s z) (chartContraction φ s w) ≤ C * s * dist z w) := by
  obtain ⟨L, hL⟩ := hbackward.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (1 : G) R)
  have hinv : φ.symm 1 = 0 := by rw [← hφ, φ.symm_apply_apply]
  have hlog (z : G) (hz : z ∈ closedBall (1 : G) R) : ‖φ.symm z‖ ≤ L * R := by
    have h := hL.dist_le_mul z hz 1 (mem_closedBall_self hR)
    rw [hinv, dist_zero_right] at h
    exact h.trans (mul_le_mul_of_nonneg_left hz L.2)
  have hB : 0 ≤ (L : ℝ) * R := mul_nonneg L.2 hR
  obtain ⟨P, hP⟩ := hforward.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : E) ((L : ℝ) * R))
  have hscaled (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (z : G)
      (hz : z ∈ closedBall (1 : G) R) : s • φ.symm z ∈ closedBall (0 : E) ((L : ℝ) * R) := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_left (hlog z hz) hs.1).trans
      (mul_le_of_le_one_left hB hs.2)
  let C : ℝ := 1 + (P : ℝ) * ((L : ℝ) * R + L)
  have hCt : (P : ℝ) * ((L : ℝ) * R) ≤ C := by dsimp [C]; nlinarith [P.2, L.2]
  have hCs : (P : ℝ) * L ≤ C := by dsimp [C]; nlinarith [P.2, hB]
  refine ⟨C, by dsimp [C]; exact le_add_of_nonneg_right (mul_nonneg P.2 (add_nonneg hB L.2)), ?_, ?_⟩
  · intro s hs t ht z hz
    have h := hP.dist_le_mul _ (hscaled s hs z hz) _ (hscaled t ht z hz)
    have he : dist (s • φ.symm z) (t • φ.symm z) = |s - t| * ‖φ.symm z‖ := by
      rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
    rw [he] at h
    calc
      _ ≤ (P : ℝ) * (|s - t| * ‖φ.symm z‖) := h
      _ ≤ (P : ℝ) * (|s - t| * ((L : ℝ) * R)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hlog z hz) (abs_nonneg _)) P.2
      _ ≤ C * |s - t| := by nlinarith only [mul_le_mul_of_nonneg_right hCt (abs_nonneg (s - t))]
  · intro s hs z hz w hw
    have h := hP.dist_le_mul _ (hscaled s hs z hz) _ (hscaled s hs w hw)
    have he : dist (s • φ.symm z) (s • φ.symm w) = s * dist (φ.symm z) (φ.symm w) := by
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1, dist_eq_norm]
    rw [he] at h
    calc
      _ ≤ (P : ℝ) * (s * dist (φ.symm z) (φ.symm w)) := h
      _ ≤ (P : ℝ) * (s * ((L : ℝ) * dist z w)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hL.dist_le_mul z hz w hw) hs.1) P.2
      _ ≤ C * s * dist z w := by
        nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCs hs.1) (dist_nonneg (x := z) (y := w))]

end PolycyclicRecognition

end

end OAI
