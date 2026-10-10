import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffMovingPath
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPhysicalSampling
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSmoothFilter

namespace OAI

/-! # The sampled cutoff coefficient agrees locally with the whole-space profile -/

open Set Filter Topology
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem sampledCutoffProfile_physical_eq (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (y : E) (hy : 2 * ‖y‖ ≤ L) :
    expandingPhysicalContinuous a k L ha ha1 hk hL
      (schwartzTorusSample a k L ha1 hk hL (radianFourierKernel
        (cutoffProfileSchwartz L (by linarith) χ hχ Q hQ))) y = Q y := by
  have hpos : 0 < L := by linarith
  rw [expandingPhysicalContinuous_apply,
    schwartzTorusSample_eq_on_ball a k L ha ha1 hk hL]
  · rw [cutoffProfileSchwartz_apply, hχone, one_mul]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    apply (inv_mul_le_iff₀ hpos).mpr
    linarith
  · intro x hx
    rw [cutoffProfileSchwartz_apply, hχzero, zero_mul]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    apply (le_inv_mul_iff₀ hpos).mpr
    linarith
  · linarith [norm_nonneg y]

theorem tendsto_sampledCutoffProfile_physical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop) (y : E) :
    Tendsto (fun n => expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n)
      (schwartzTorusSample a k (L n) ha1 hk (hL n) (radianFourierKernel
        (cutoffProfileSchwartz (L n) (by linarith [hL n]) χ hχ Q hQ))) y)
      atTop (𝓝 (Q y)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [hLinf.eventually (eventually_ge_atTop (2 * ‖y‖))] with n hn
  exact (sampledCutoffProfile_physical_eq a k (L n) ha ha1 hk (hL n)
    χ hχ hχzero hχone Q hQ y hn).symm

theorem tendsto_sampledCutoffProfilePath_physical (a k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (s : Icc (0 : ℝ) T) (y : E) :
    Tendsto (fun n => expandingPhysicalContinuous a k (expandingRadius (L n) s)
      ha ha1 hk ((hL n).trans (expandingRadius_ge (L n) s (hL n) s.2.1))
      (sampledCutoffProfilePath a k (L n) T ha ha1 hk (hL n) χ hχ Q hQ s) y)
      atTop (𝓝 (Q y)) := by
  exact tendsto_sampledCutoffProfile_physical a k ha ha1 hk χ hχ hχzero hχone Q hQ
    (fun n => expandingRadius (L n) s)
    (fun n => (hL n).trans (expandingRadius_ge (L n) s (hL n) s.2.1))
    (hLinf.atTop_mul_const (Real.exp_pos _)) y

end DefocusingNLS

end OAI
