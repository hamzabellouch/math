import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzCutoffDerivative

namespace OAI

/-! # Uniform bound for the cutoff's directional derivative term -/

open scoped SchwartzMap LineDeriv ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem cutoff_directional_sum (L : ℝ) (hL : 0 < L)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (v : E) :
    cutoffProfileSchwartz L hL (∂_{v} χ) (schwartzCutoff_lineDeriv_compact χ hχ v) Q hQ =
      ∑ j : Fin 12, (v j) • cutoffProfileSchwartz L hL
        (∂_{(EuclideanSpace.basisFun (Fin 12) ℝ) j} χ)
        (schwartzCutoff_lineDeriv_compact χ hχ _) Q hQ := by
  ext y
  have hrep : (∑ j : Fin 12, v j • (EuclideanSpace.basisFun (Fin 12) ℝ) j) = v := by
    simpa only [EuclideanSpace.basisFun_repr] using (EuclideanSpace.basisFun (Fin 12) ℝ).sum_repr v
  have he := congrArg (fderiv ℝ (χ : E → ℂ) (L⁻¹ • y)) hrep
  simp only [map_sum, map_smul] at he
  simp only [cutoffProfileSchwartz_apply, sum_apply, smul_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, Complex.real_smul]
  rw [← he]
  simp only [Finset.sum_mul, Complex.real_smul, mul_assoc]

theorem cutoff_directional_sample_bound (a k : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L) (v : E),
      ‖physicalSchwartzTorusSamplingCLM a k L ha1 hk hL
        (cutoffProfileSchwartz L (by linarith) (∂_{v} χ)
          (schwartzCutoff_lineDeriv_compact χ hχ v) Q hQ)‖ ≤ C * ‖v‖ := by
  classical
  have hb (j : Fin 12) := cutoffProfile_sampling_of_global_symbol a k ha ha1 hk
    (∂_{(EuclideanSpace.basisFun (Fin 12) ℝ) j} χ)
    (schwartzCutoff_lineDeriv_compact χ hχ _)
    (schwartzCutoff_lineDeriv_zero χ hχzero _) Q hQ hsymbol
  choose B hB hbound using hb
  refine ⟨∑ j, B j, Finset.sum_nonneg (fun j _ => hB j), ?_⟩
  intro L hL v
  rw [cutoff_directional_sum L (by linarith) χ hχ Q hQ v, map_sum]
  calc
    _ ≤ ∑ j : Fin 12, ‖physicalSchwartzTorusSamplingCLM a k L ha1 hk hL
        ((v j) • cutoffProfileSchwartz L (by linarith)
          (∂_{(EuclideanSpace.basisFun (Fin 12) ℝ) j} χ)
          (schwartzCutoff_lineDeriv_compact χ hχ _) Q hQ)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 12, ‖v‖ * B j := by
      apply Finset.sum_le_sum
      intro j _
      rw [ContinuousLinearMap.map_smul_of_tower, norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le v j) (hbound j L hL)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem cutoff_directional_error_bound (a k : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L) (v : E),
      ‖physicalSchwartzTorusSamplingCLM a k L ha1 hk hL
          (∂_{v} (cutoffProfileSchwartz L (by linarith) χ hχ Q hQ)) -
        physicalSchwartzTorusSamplingCLM a k L ha1 hk hL
          (cutoffProfileSchwartz L (by linarith) χ hχ (cartesianDerivative v Q)
            (cartesianDerivative_contDiff Q hQ v))‖ ≤ C / L * ‖v‖ := by
  obtain ⟨C, hC, hb⟩ := cutoff_directional_sample_bound a k ha ha1 hk χ hχ hχzero Q hQ hsymbol
  refine ⟨C, hC, ?_⟩
  intro L hL v
  rw [cutoffProfileSchwartz_lineDeriv L (by linarith) χ hχ Q hQ v, map_add,
    add_sub_cancel_left, ContinuousLinearMap.map_smul_of_tower, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by linarith : 0 < L))]
  calc
    _ ≤ L⁻¹ * (C * ‖v‖) := mul_le_mul_of_nonneg_left (hb L hL v) (by positivity)
    _ = _ := by ring

end DefocusingNLS

end OAI
