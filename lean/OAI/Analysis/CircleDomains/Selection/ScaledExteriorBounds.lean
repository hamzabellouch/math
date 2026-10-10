import OAI.Analysis.CircleDomains.Uniformization.ExteriorCoefficientBounds

namespace OAI

/-!
# Exterior bounds at a prescribed physical radius

Scaling a principally normalized exterior map to the unit exterior
preserves its normalization. The coefficient-area input then bounds
its deviation from the identity outside twice the prescribed radius.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem principal_remainder_rescale {F : ℂ → ℂ} {a : ℂ} (ha : a ≠ 0)
    (hF : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    (fun z => F (a * z) / a - z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  have hs := hF.comp_tendsto (tendsto_mul_left_cobounded ha)
  have hi : (fun z : ℂ => (a * z)⁻¹) =O[cobounded ℂ] (fun z => z⁻¹) := by
    simpa only [smul_eq_mul, mul_inv_rev, mul_comm] using
      (IsBigO.const_smul_self (f' := fun z : ℂ => z⁻¹) (l := cobounded ℂ) a⁻¹)
  have hm := (hs.trans hi).const_smul_left a⁻¹
  apply hm.congr_left
  intro z
  change a⁻¹ * (F (a * z) - a * z) = F (a * z) / a - z
  field_simp

theorem ExteriorCoefficientAreaTheorem.scaled_exterior_bound
    (harea : ExteriorCoefficientAreaTheorem) {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (hinj : InjOn F {z | R < ‖z‖})
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖F z - z‖ ≤ R := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hnormR : ‖(R : ℂ)‖ = R := by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  let H : ℂ → ℂ := fun z => F ((R : ℂ) * z) / (R : ℂ)
  have harg {z : ℂ} (hz : 1 < ‖z‖) : R < ‖(R : ℂ) * z‖ := by
    rw [norm_mul, hnormR]
    nlinarith
  have hH : DifferentiableOn ℂ H {z | 1 < ‖z‖} := by
    intro z hz
    have hfd := (hF _ (harg hz)).differentiableAt
      ((isOpen_lt continuous_const continuous_norm).mem_nhds (harg hz))
    exact ((hfd.comp z ((differentiableAt_id.const_mul (R : ℂ)))).div_const _).differentiableWithinAt
  have hHi : InjOn H {z | 1 < ‖z‖} := by
    intro z hz w hw heq
    have heq' : F ((R : ℂ) * z) = F ((R : ℂ) * w) := (div_left_inj' hRc).mp heq
    exact mul_left_cancel₀ hRc (hinj (harg hz) (harg hw) heq')
  have hnH := principal_remainder_rescale hRc hnorm
  intro z hz
  have hnormquot : ‖z / (R : ℂ)‖ = ‖z‖ / R := by rw [norm_div, hnormR]
  have hquot : 2 ≤ ‖z / (R : ℂ)‖ := by
    rw [hnormquot]
    exact (le_div_iff₀ hR).mpr (by linarith)
  have hb := harea.exterior_bound hH hHi hnH (z / (R : ℂ)) hquot
  have heq : H (z / (R : ℂ)) - z / (R : ℂ) = (F z - z) / (R : ℂ) := by
    dsimp only [H]
    rw [mul_div_cancel₀ z hRc]
    ring
  rw [heq, norm_div, hnormR] at hb
  exact (div_le_one hR).mp hb

end CircleDomainRigidity

end

end OAI
