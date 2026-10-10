import OAI.NumberTheory.JointDickman.Analysis.MellinPacketScale
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace OAI

/-! # Smooth inner approximations to a logarithmic interval -/
namespace JointDickman
open scoped SchwartzMap

noncomputable def logarithmicWindowBump (η : ℝ) (hη : 0 < η) (hηhalf : η < 1/2) :
    ContDiffBump (1/2 : ℝ) where
  rIn := 1/2 - η
  rOut := 1/2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

noncomputable def logarithmicWindowProfile (η : ℝ) (hη : 0 < η) (hηhalf : η < 1/2) :
    𝓢(ℝ, ℂ) :=
  ((logarithmicWindowBump η hη hηhalf).hasCompactSupport.toSchwartzMap
    (logarithmicWindowBump η hη hηhalf).contDiff).postcompCLM Complex.ofRealCLM

theorem logarithmicWindowProfile_apply (η : ℝ) (hη : 0 < η) (hηhalf : η < 1/2)
    (v : ℝ) : logarithmicWindowProfile η hη hηhalf v =
      ((logarithmicWindowBump η hη hηhalf v : ℝ) : ℂ) := rfl

theorem logarithmicWindowProfile_norm_le (η : ℝ) (hη : 0 < η)
    (hηhalf : η < 1/2) (v : ℝ) : ‖logarithmicWindowProfile η hη hηhalf v‖ ≤ 1 := by
  rw [logarithmicWindowProfile_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (logarithmicWindowBump η hη hηhalf).nonneg]
  exact (logarithmicWindowBump η hη hηhalf).le_one

theorem logarithmicWindowProfile_one (η : ℝ) (hη : 0 < η)
    (hηhalf : η < 1/2) {v : ℝ} (hv : v ∈ Set.Icc η (1 - η)) :
    logarithmicWindowProfile η hη hηhalf v = 1 := by
  rw [logarithmicWindowProfile_apply]
  have hh : logarithmicWindowBump η hη hηhalf v = 1 := by
    apply (logarithmicWindowBump η hη hηhalf).one_of_mem_closedBall
    change dist v (1/2 : ℝ) ≤ 1/2 - η
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hv.1, hv.2]
  rw [hh, Complex.ofReal_one]

theorem logarithmicWindowProfile_zero (η : ℝ) (hη : 0 < η)
    (hηhalf : η < 1/2) {v : ℝ} (hv : v ≤ 0 ∨ 1 ≤ v) :
    logarithmicWindowProfile η hη hηhalf v = 0 := by
  rw [logarithmicWindowProfile_apply]
  have hh : logarithmicWindowBump η hη hηhalf v = 0 := by
    apply (logarithmicWindowBump η hη hηhalf).zero_of_le_dist
    change (1/2 : ℝ) ≤ dist v (1/2 : ℝ)
    rw [Real.dist_eq]
    rcases hv with hv | hv
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  rw [hh, Complex.ofReal_zero]

end JointDickman

end OAI
