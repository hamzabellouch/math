import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicTestCalculus
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

namespace OAI

/-! # Compact annular harmonic tests

A compact scalar test in the positive squared radius removes the apparent
singularity of a degree-zero angular extension at the origin.
-/

open Set Filter Topology
open scoped ContDiff SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def squaredHarmonicTest (ψ : 𝓢(ℝ, ℂ)) (Y : E → ℂ) (x : E) : ℂ :=
  ψ (‖x‖ ^ 2) * Y x

theorem squaredHarmonicTest_contDiff (ψ : 𝓢(ℝ, ℂ)) (Y : E → ℂ)
    (hs : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hY : ∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x) :
    ContDiff ℝ ∞ (squaredHarmonicTest ψ Y) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have hz : (0 : ℝ) ∉ tsupport ψ := fun h => (lt_irrefl 0) (Set.mem_Ioi.mp (hs h))
    have he : (fun y : E => ψ (‖y‖ ^ 2)) =ᶠ[𝓝 0] (fun _ => (0 : ℂ)) := by
      have ht := (notMem_tsupport_iff_eventuallyEq.mp hz)
      have hn : Tendsto (fun y : E => ‖y‖ ^ 2) (𝓝 0) (𝓝 0) := by
        have hcont : Continuous (fun y : E => ‖y‖ ^ 2) := by fun_prop
        simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
          hcont.tendsto (0 : E)
      exact ht.comp_tendsto hn
    have he' : squaredHarmonicTest ψ Y =ᶠ[𝓝 0] (fun _ => (0 : ℂ)) := by
      filter_upwards [he] with y hy
      simp only [squaredHarmonicTest, hy, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he'
  · exact ((ψ.smooth ⊤).contDiffAt.comp x (contDiff_norm_sq ℝ).contDiffAt).mul (hY x hx)

theorem squaredHarmonicTest_hasCompactSupport (ψ : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport ψ) (Y : E → ℂ) :
    HasCompactSupport (squaredHarmonicTest ψ Y) := by
  obtain ⟨B, hB⟩ := hc.isBounded.exists_norm_le
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) (max B 1))
  intro x hx
  have hψ : ψ (‖x‖ ^ 2) ≠ 0 := by
    intro hz
    exact hx (by simp [squaredHarmonicTest, hz])
  have hs := hB (‖x‖ ^ 2) (subset_tsupport ψ (Function.mem_support.mpr hψ))
  have hs' : ‖x‖ ^ 2 ≤ B := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖x‖))] using hs
  change dist x 0 ≤ max B 1
  rw [dist_zero_right]
  have hb := le_max_left B (1 : ℝ)
  have hb1 := le_max_right B (1 : ℝ)
  nlinarith [sq_nonneg (‖x‖ - 1)]

/-- The actual Schwartz test used in the Cartesian weak equation. -/
noncomputable def squaredHarmonicSchwartz (ψ : 𝓢(ℝ, ℂ)) (Y : E → ℂ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hY : ∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x) : 𝓢(E, ℂ) :=
  (squaredHarmonicTest_hasCompactSupport ψ hc Y).toSchwartzMap
    (squaredHarmonicTest_contDiff ψ Y hs hY)

@[simp] theorem squaredHarmonicSchwartz_apply (ψ : 𝓢(ℝ, ℂ)) (Y : E → ℂ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hY : ∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x) (x : E) :
    squaredHarmonicSchwartz ψ Y hc hs hY x = ψ (‖x‖ ^ 2) * Y x := rfl

end DefocusingNLS

end OAI
