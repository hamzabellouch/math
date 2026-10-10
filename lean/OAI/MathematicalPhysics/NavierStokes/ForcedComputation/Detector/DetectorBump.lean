import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusScalarInput

namespace OAI

/-! The nonnegative height-one periodic bump injected by a detector block.
Its center is the fixed planar processor point (1/4,1/4). -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

def detectorProfile (b : ℝ) : ℝ → ℝ :=
  circleCutoff 1 (1 / 4 - b) (1 / 4 - b / 2) (1 / 4 + b / 2) (1 / 4 + b)

def detectorBump (b : ℝ) (x : Plane) : ℝ :=
  detectorProfile b (x 0) * detectorProfile b (x 1)

theorem detectorProfile_smooth {b : ℝ} (hb : 0 < b) :
    ContDiff ℝ ∞ (detectorProfile b) :=
  circleCutoff_smooth (by norm_num) (by linarith) (by linarith)

theorem detectorProfile_periodic (b : ℝ) : Function.Periodic (detectorProfile b) 1 :=
  circleCutoff_periodic _ _ _ _ _

theorem detectorProfile_in_chart {b x : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1 / 16)
    (hx : x ∈ Icc 0 1) :
    detectorProfile b x =
      closedCutoff (1 / 4 - b) (1 / 4 - b / 2) (1 / 4 + b / 2) (1 / 4 + b) x := by
  exact circleCutoff_eq_in_chart (A := 0) (B := 1) (by norm_num) (by norm_num)
    (by linarith) (by linarith) (by linarith) (by linarith) hx

theorem detectorProfile_range {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1 / 16) (x : ℝ) :
    detectorProfile b x ∈ Icc (0 : ℝ) 1 := by
  have he : detectorProfile b (Int.fract x) = detectorProfile b x := by
    simpa only [Int.fract, mul_one] using
      (detectorProfile_periodic b).sub_int_mul_eq (x := x) ⌊x⌋
  rw [← he, detectorProfile_in_chart hb hb₁ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩]
  exact closedCutoff_range _ _ _ _ _

theorem detectorProfile_center {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1 / 16) :
    detectorProfile b (1 / 4) = 1 := by
  rw [detectorProfile_in_chart hb hb₁ (by norm_num)]
  exact closedCutoff_plateau (by linarith) (by linarith) ⟨by linarith, by linarith⟩

theorem detectorBump_smooth {b : ℝ} (hb : 0 < b) :
    ContDiff ℝ ∞ (detectorBump b) :=
  ((detectorProfile_smooth hb).comp (contDiff_apply ℝ ℝ 0)).mul
    ((detectorProfile_smooth hb).comp (contDiff_apply ℝ ℝ 1))

theorem detectorBump_periodic (b : ℝ) : PlanePeriodic (detectorBump b) := by
  intro x n
  have h₀ := (detectorProfile_periodic b).int_mul (n 0) (x 0)
  have h₁ := (detectorProfile_periodic b).int_mul (n 1) (x 1)
  simpa only [detectorBump, Pi.add_apply, mul_one] using congrArg₂ (· * ·) h₀ h₁

theorem detectorBump_range {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1 / 16) (x : Plane) :
    detectorBump b x ∈ Icc (0 : ℝ) 1 := by
  have h₀ := detectorProfile_range hb hb₁ (x 0)
  have h₁ := detectorProfile_range hb hb₁ (x 1)
  exact ⟨mul_nonneg h₀.1 h₁.1, (mul_le_mul h₀.2 h₁.2 h₁.1 (by norm_num)).trans_eq (mul_one 1)⟩

theorem detectorBump_center {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1 / 16) :
    detectorBump b ![1 / 4, 1 / 4] = 1 := by
  change detectorProfile b (1 / 4) * detectorProfile b (1 / 4) = 1
  rw [detectorProfile_center hb hb₁, mul_one]

theorem detectorBump_support_in_chart {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1 / 16)
    {x : Plane} (hx : ∀ j, x j ∈ Icc (0 : ℝ) 1) (hn : detectorBump b x ≠ 0) :
    ∀ j, |x j - 1 / 4| < b := by
  have hprod : detectorProfile b (x 0) ≠ 0 ∧ detectorProfile b (x 1) ≠ 0 :=
    mul_ne_zero_iff.mp hn
  intro j
  have hj : detectorProfile b (x j) ≠ 0 := by
    fin_cases j
    · exact hprod.1
    · exact hprod.2
  rw [detectorProfile_in_chart hb hb₁ (hx j)] at hj
  have hs := closedCutoff_support (a := 1 / 4 - b) (b := 1 / 4 - b / 2)
    (c := 1 / 4 + b / 2) (d := 1 / 4 + b) (by linarith) (by linarith) hj
  exact abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩

end ForcedComputation.VelocityDetector

end

end OAI
