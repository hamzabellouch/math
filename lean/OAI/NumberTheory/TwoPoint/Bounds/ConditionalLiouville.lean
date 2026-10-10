import OAI.NumberTheory.TwoPoint.Bounds.QuantitativeFixedScale
import OAI.NumberTheory.TwoPoint.Bounds.ProgressionMeanIdentity
import OAI.NumberTheory.TwoPoint.QuantitativeAffineTransfer
import OAI.NumberTheory.TwoPoint.Bounds.LogSavingScale

namespace OAI

/-! The manuscript's quantitative main theorem, conditional only on the
named published prime, circuit, and Liouville short-sum inputs. -/

namespace TwoPointCorrelations

open Filter

theorem conditional_liouville_progression (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ h l b : ℕ, 0 < h → 0 < l →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
        ‖progressionSum liouville liouville h l b ⌊X⌋₊‖ ≤
          C * X / (Real.log X) ^ c := by
  obtain ⟨A, W, hA, hW, hb⟩ := quantitative_fixed_scale hP hBr hM hMRT
  have hAp : 0 < A := by omega
  have hWp : 0 < W := by linarith
  let c : ℝ := 1 / (1200 * W * A)
  refine ⟨c, log_saving_exponent_pos W A hWp hAp, ?_⟩
  intro h l b hh hl
  let : NeZero l := ⟨by omega⟩
  obtain ⟨C, hC, hb⟩ := hb h l hh
  refine ⟨C * Real.exp 1, by positivity, ?_⟩
  filter_upwards [(final_log_scale_tendsto A hAp).eventually hb,
    eventually_ge_atTop (Real.exp 1)] with X hb hX
  have hXone : 1 ≤ X := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hX
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX
  have hm := hb X (by rw [final_log_scale_exact X A hXone (by omega)]) b
  rw [progressionLiouvilleMean_eq, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hXp] at hm
  have hs := mul_le_mul_of_nonneg_left (primeSupplyCount_log_saving X W A hX hWp hAp) hC.le
  have hm' := (div_le_iff₀ hXp).mp (hm.trans hs)
  change ‖progressionSum liouville liouville h l b ⌊X⌋₊‖ ≤ _
  convert hm' using 1; ring

theorem conditional_liouvilleLogSaving (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) : LiouvilleLogSaving :=
  liouvilleLogSaving_of_progression (conditional_liouville_progression hP hBr hM hMRT)

end TwoPointCorrelations

end OAI
