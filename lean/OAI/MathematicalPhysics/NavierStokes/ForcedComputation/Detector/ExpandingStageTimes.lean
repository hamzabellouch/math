import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingDetectorScales
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorBlockSum

namespace OAI

/-! Explicit stage times tend to infinity, so the expanding-array bursts
form a locally finite smooth sum. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Set
open scoped BigOperators ContDiff

theorem initialRadius_ge_one {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) :
    1 ≤ initialRadius ν D K := by
  have he : 1 ≤ expansion D := by linarith [expansion_ge_four hD]
  have hk : 1 ≤ K * D + 2 := by
    nlinarith [mul_nonneg hK (show 0 ≤ D by linarith)]
  have ha : 1 ≤ 1024 * 3000 * (1 + ν) := by linarith
  have h₁ : 1 ≤ (1024 * 3000 * (1 + ν)) * expansion D := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr he)]
  unfold initialRadius
  nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr hk)]

theorem radius_ge_one {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) (n : ℕ) :
    1 ≤ radius ν D K n := by
  induction n with
  | zero => simpa only [radius, pow_zero, mul_one] using initialRadius_ge_one hν hD hK
  | succ n ih =>
    have hg := radius_grows hν hD hK n
    linarith

theorem duration_ge_two {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) (n : ℕ) :
    2 ≤ duration ν D K n := by
  have hr := radius_ge_one hν hD hK (n + 1)
  have hc : 2 ≤ K * D ^ (n + 1) + 2 := by
    have hn := mul_nonneg hK (pow_nonneg (show 0 ≤ D by linarith) (n + 1))
    linarith
  unfold duration
  nlinarith [mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ K * D ^ (n + 1) + 2 by linarith)]

def stageStart (ν D K : ℝ) (n : ℕ) : ℝ := 2 + ∑ i ∈ Finset.range n, duration ν D K i

@[simp] theorem stageStart_zero (ν D K : ℝ) : stageStart ν D K 0 = 2 := by
  simp [stageStart]

theorem stageStart_succ (ν D K : ℝ) (n : ℕ) :
    stageStart ν D K (n + 1) = stageStart ν D K n + duration ν D K n := by
  simp only [stageStart, Finset.sum_range_succ]
  ring

theorem stageStart_ge {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) (n : ℕ) :
    2 * ((n : ℝ) + 1) ≤ stageStart ν D K n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [stageStart_succ]
    have ht := duration_ge_two hν hD hK n
    push_cast
    linarith

theorem stageStart_strictMono {ν D K : ℝ}
    (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) : StrictMono (stageStart ν D K) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [stageStart_succ]
  linarith [duration_ge_two hν hD hK n]

theorem expanding_burst_sum_smooth {ν D K : ℝ}
    (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (F : ℕ → ℝ × Plane → ℝ) (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hbefore : ∀ n y, y.1 < stageStart ν D K n → F n y = 0) :
    ContDiff ℝ ∞ (VelocityDetector.detectorBlockSum F) := by
  apply VelocityDetector.detectorBlockSum_smooth F hF
  intro n y hy
  exact hbefore n y (hy.trans_le (stageStart_ge hν hD hK n))

end ForcedComputation.ExpandingDetector

end

end OAI
