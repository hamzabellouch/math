import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSampleTranslation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDerivativeWeight

namespace OAI

/-! # Uniform sampling estimates for directional derivatives -/

open scoped SchwartzMap LineDeriv RealInnerProductSpace ENNReal
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem schwartzSample_directional_norm_le (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (hL : 1 ≤ L) (ψ : 𝓢(E, ℂ)) (v : E) :
    ‖physicalSchwartzTorusSamplingCLM a k L ha1 hk hL (∂_{v} ψ)‖ ≤
      (2 ^ (6 - a) + 1) * ‖v‖ *
        ‖physicalSchwartzTorusSamplingCLM a (k + 1) L ha1 (by linarith) hL ψ‖ := by
  let C := (2 : ℝ) ^ (6 - a) + 1
  let g := physicalSchwartzTorusSamplingCLM a (k + 1) L ha1 (by linarith) hL ψ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (n : frequencyLattice) :
      ‖physicalSchwartzTorusSamplingCLM a k L ha1 hk hL (∂_{v} ψ) n‖ ≤
        C * ‖v‖ * ‖g n‖ := by
    have hxi : ‖L⁻¹ • (n : E)‖ = ‖n‖ / L := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith : 0 < L)]
      simp only [Submodule.norm_coe, div_eq_inv_mul]
    have hi : |inner ℝ (L⁻¹ • (n : E)) v| ≤ (‖n‖ / L) * ‖v‖ := by
      simpa only [hxi] using abs_real_inner_le_norm (L⁻¹ • (n : E)) v
    have hf : expandingSobolevWeight a k L n * |inner ℝ (L⁻¹ • (n : E)) v| ≤
        C * ‖v‖ * expandingSobolevWeight a (k + 1) L n := by
      calc
        _ ≤ expandingSobolevWeight a k L n * ((‖n‖ / L) * ‖v‖) :=
          mul_le_mul_of_nonneg_left hi (expandingSobolevWeight_pos a k L hL n).le
        _ = (expandingSobolevWeight a k L n * (‖n‖ / L)) * ‖v‖ := by ring
        _ ≤ (C * expandingSobolevWeight a (k + 1) L n) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (expandingSobolevWeight_derivative_le a k L ha ha1 hk hL n)
            (norm_nonneg v)
        _ = _ := by ring
    simp only [physicalSchwartzTorusSamplingCLM_apply, g]
    change ‖(expandingSobolevWeight a k L n : ℂ) *
      schwartzLatticeCoefficient L (radianFourierKernel (∂_{v} ψ)) n‖ ≤
      C * ‖v‖ * ‖(expandingSobolevWeight a (k + 1) L n : ℂ) *
        schwartzLatticeCoefficient L (radianFourierKernel ψ) n‖
    simp only [schwartzLatticeCoefficient, radianFourierKernel_lineDeriv, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      abs_of_pos (expandingSobolevWeight_pos a k L hL n),
      abs_of_pos (expandingSobolevWeight_pos a (k + 1) L hL n)]
    have hm := mul_le_mul_of_nonneg_right hf
      (show 0 ≤ |((2 * Real.pi * L) ^ (12 : ℕ))⁻¹| *
        ‖radianFourierKernel ψ (L⁻¹ • (n : E))‖ by positivity)
    nlinarith only [hm]
  calc
    _ ≤ ‖(C * ‖v‖ : ℝ) • g‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hC (norm_nonneg v))] using hbound n
    _ = _ := by rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hC (norm_nonneg v))]

theorem schwartzSample_secondDirectional_norm_le (a k L : ℝ) (ha : 0 < a)
    (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (ψ : 𝓢(E, ℂ)) (v : E) :
    ‖physicalSchwartzTorusSamplingCLM a k L ha1 hk hL (∂_{v} (∂_{v} ψ))‖ ≤
      (2 ^ (6 - a) + 1) ^ 2 * ‖v‖ ^ 2 *
        ‖physicalSchwartzTorusSamplingCLM a (k + 2) L ha1 (by linarith) hL ψ‖ := by
  have h1 := schwartzSample_directional_norm_le a k L ha ha1 hk hL (∂_{v} ψ) v
  have h2 := schwartzSample_directional_norm_le a (k + 1) L ha ha1 (by linarith) hL ψ v
  have he : k + 1 + 1 = k + 2 := by ring
  simp only [he] at h2
  calc
    _ ≤ (2 ^ (6 - a) + 1) * ‖v‖ *
        ((2 ^ (6 - a) + 1) * ‖v‖ *
          ‖physicalSchwartzTorusSamplingCLM a (k + 2) L ha1 (by linarith) hL ψ‖) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by ring

end DefocusingNLS

end OAI
