import OAI.NumberTheory.TwoPointCorrelations.HalaszUnitRenormalization
import OAI.NumberTheory.TwoPointCorrelations.HalaszGeneralTwist

namespace OAI

/-! Uniform renormalization on the small neighborhood of the minimizing twist.
This is the near-twist ingredient needed for the MRT Fourier energy estimate. -/

namespace TwoPointCorrelations

open Finset Filter

/-- The elementary unit-correction argument loses only `log(N)^(-1/16)`
on the whole near-center frequency interval. -/
theorem halasz_near_renormalization :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ t : ℝ, squaredDistance F (mrtArchimedeanTwist t) N ≤
        Real.log (Real.log N) / 8 →
      ∀ u : ℝ, |u| ≤ (Real.log N) ^ (1 / (16 : ℝ)) →
      let G := halaszTwistedFunction (mrtMissingCoefficient F Q) t
      ‖halaszPhaseMean G u N -
        (halaszPowerPhase u N / (1 + (-u : ℂ) * Complex.I)) * halaszPhaseMean G 0 N‖ ≤
      (36 * (halaszPrimePowerLogConstant + 1) * Real.exp 8) * N *
        (Real.log N) ^ (-1 / (16 : ℝ)) := by
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [halasz_near_correction_mean, hlog] with N hmean hlogN
  intro F hF1 hFm hFb Q hQ hcut t hD u hu
  dsimp only
  let G := halaszTwistedFunction (mrtMissingCoefficient F Q) t
  have hGm : Multiplicative G := halasz_twisted_multiplicative _
    (mrtMissingCoefficient_multiplicative F hFm Q hQ) t
  have hG1 : G 1 = 1 := halasz_twisted_one _ (mrtMissingCoefficient_one F hF1 Q hQ) t
  have hh := halasz_unit_renormalization G hGm hG1 u N
  have hm := hmean F hF1 hFb Q hQ hcut t hD
  have hl : 0 < Real.log (N : ℝ) := by linarith
  have hp : 1 ≤ (Real.log N) ^ (1 / (16 : ℝ)) := Real.one_le_rpow hlogN (by norm_num)
  have hb : 18 * (1 + |u|) ≤ 36 * (Real.log N) ^ (1 / (16 : ℝ)) := by linarith
  have hc : 0 ≤ (halaszPrimePowerLogConstant + 1) * Real.exp 8 := by
    unfold halaszPrimePowerLogConstant
    positivity
  have he : (Real.log N) ^ (1 / (16 : ℝ)) * (Real.log N) ^ (-1 / (8 : ℝ)) =
      (Real.log N) ^ (-1 / (16 : ℝ)) := by
    rw [← Real.rpow_add hl]
    norm_num
  apply hh.trans
  calc
    _ ≤ (36 * (Real.log N) ^ (1 / (16 : ℝ))) *
        (((halaszPrimePowerLogConstant + 1) * Real.exp 8) * N *
          (Real.log N) ^ (-1 / (8 : ℝ))) := by
      exact mul_le_mul hb hm (sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _ = (36 * (halaszPrimePowerLogConstant + 1) * Real.exp 8) * N *
        ((Real.log N) ^ (1 / (16 : ℝ)) * (Real.log N) ^ (-1 / (8 : ℝ))) := by ring
    _ = _ := by rw [he]

end TwoPointCorrelations

end OAI
