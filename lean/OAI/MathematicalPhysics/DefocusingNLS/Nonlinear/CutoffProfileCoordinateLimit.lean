import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffProfilePhysicalLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalWeakLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLocalizationPhysical
import OAI.MathematicalPhysics.DefocusingNLS.Linear.WeakLinearCoordinates

namespace OAI

/-! # Finite coordinates of the actual sampled profile converge to its whole-space coordinates -/

open Filter Topology
open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem cutoffProfile_finite_coordinate_limit (a k : ℝ) (ha : 0 < a)
    (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ))
    (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (q : HomogeneousY a k)
    (hq : ∀ y, homogeneousPhysicalCLM a k ha ha1 hk q y = Q y)
    (B : ℝ) (_hB : 0 ≤ B)
    (hb : ∀ (L : ℝ) (hL : 1 ≤ L),
      ‖physicalSchwartzTorusSamplingCLM a k L ha1 hk hL
        (cutoffProfileSchwartz L (by linarith) χ hχ Q hQ)‖ ≤ B)
    (L : ℕ → Radius) (hLinf : Tendsto (fun n => (L n).1) atTop atTop)
    (π : HomogeneousY a k →L[ℝ] F) :
    Tendsto (fun n => π (homogeneousLocalizationCLM a k (L n).1 ha ha1 hk (L n).2 χ
      (physicalSchwartzTorusSamplingCLM a k (L n).1 ha1 hk (L n).2
        (cutoffProfileSchwartz (L n).1 (by linarith [(L n).2]) χ hχ Q hQ))))
      atTop (𝓝 (π q)) := by
  obtain ⟨D, hD, hd⟩ := exists_homogeneousLocalization_bound a k ha ha1 hk χ
  apply tendsto_finite_coordinates_of_weak π _ q
  apply homogeneousY_weak_of_physical_limit a k (D * B) ha ha1 hk
  · intro n
    exact (hd (L n).1 (L n).2 _).trans (mul_le_mul_of_nonneg_left (hb (L n).1 (L n).2) hD)
  · intro y
    rw [hq]
    apply tendsto_const_nhds.congr'
    filter_upwards [hLinf.eventually (eventually_ge_atTop (2 * ‖y‖))] with n hn
    rw [homogeneousLocalization_physical, expandingPhysicalLocalization]
    have hc : χ ((L n).1⁻¹ • y) = 1 := by
      apply hχone
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith [(L n).2]))]
      exact (inv_mul_le_iff₀ (by linarith [(L n).2] : 0 < (L n).1)).mpr (by linarith)
    rw [hc, one_mul]
    simpa only [expandingPhysicalContinuous_apply, physicalSchwartzTorusSamplingCLM_apply] using
      (sampledCutoffProfile_physical_eq a k (L n).1 ha ha1 hk (L n).2 χ hχ
      hχzero hχone Q hQ y hn).symm

end DefocusingNLS

end OAI
