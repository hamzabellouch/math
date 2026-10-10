import OAI.NumberTheory.TwoPoint.Bounds.QualitativeRoughFourier
import OAI.NumberTheory.TwoPoint.Bounds.QualitativeSquareWindows
import OAI.NumberTheory.TwoPoint.Bounds.QualitativeStrongScale
import OAI.NumberTheory.TwoPoint.Bounds.QualitativeShiftScale
import OAI.NumberTheory.TwoPoint.Bounds.WeightedShiftParameters

namespace OAI

/-! The stronger qualitative rough-shift estimate on exp(C B²) scales, uniform over finite-prime
modifications, progression classes, and bounded rough coefficients. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

/-- The rough analytic transfer for a nonpretentious first factor.
All parameters other than the long average length are fixed before its
limit; the bound is uniform over the allowed modified functions. -/
theorem qualitative_strong_rough_shifts (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (P : Finset ℕ) (D : ℕ),
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ᶠ Y : ℕ in atTop, ∀ b g : ℕ → ℂ,
      Multiplicative b → OneBounded b → OneBounded g →
      (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
      ∀ (l : ℕ) [NeZero l] (a : ZMod l) (Z : Finset ℕ) (c : ℕ → ℂ),
      (∀ z ∈ Z, D ≤ z ∧ z < D + D ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      (∀ z ∈ Z, ‖c z‖ ≤ 1) →
      ‖weightedRoughShiftAverage (progressionSequence b l a) g Z c h Y‖ ≤
        C * B ^ (-11 / 10 : ℝ) := by
  obtain ⟨U, V, hU, hV, hfourier⟩ := hM.qualitative_rough_fourier
  obtain ⟨K, hK, hwindows⟩ := hMRT.qualitative_square_window_scale hfnp hf C₀ hC₀
  let C := 2 + (2 * (h : ℝ) + 1) + (2 * (h : ℝ) + 1) * U * V * K
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hfourier, hwindows, eventually_strong_qualitative_frequency_gap,
    eventually_qualitative_interval_lower, eventually_ge_atTop (Real.exp 1)] with
    B hfour hwin hgap hlower hB
  intro P D hDlower hDupper
  have hDten : 10 ≤ D := hlower D hDlower
  have hDpos : 0 < D := by omega
  have hBpos : 0 < B := (Real.exp_pos 1).trans_le hB
  have hlog : 0 ≤ Real.log B := Real.log_nonneg
    ((Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hB)
  have hη : 0 < B ^ (-11 / 10 : ℝ) := Real.rpow_pos_of_pos hBpos _
  filter_upwards [hwin P D hDten hDlower hDupper,
    eventually_fixed_interval_endpoint D _ hη] with Y hy hend
  intro b g hb hbounded hg heq l _ a Z c hZ hc
  have hF := hy b hb hbounded heq l a
  have hfourZ := hfour D h hDlower hh Z c hZ hc
  have hZinterval : ∀ z ∈ Z, D ≤ z ∧ z < D + D :=
    fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.1⟩
  have hZend : ∀ z ∈ Z, z ≤ 2 * D := by
    intro z hz
    have ht := (hZ z hz).2.1
    omega
  apply weighted_rough_shift_parameter_bound (progressionSequence b l a) g
    (hbounded.progressionSequence l a) hg Z c D h Y hDpos hend.1 hZend
    (Real.log B / B ^ (9999 / 10000 : ℝ)) (B ^ (-11 / 10 : ℝ)) U V K
    (by positivity) hη hU.le hV.le hK.le
    (rough_coefficient_mass_le_one Z c D hDpos hZinterval hc)
    hend.2 hgap hfourZ.1 hfourZ.2
  intro θ
  convert hF θ using 1
  ring

end TwoPointCorrelations

end OAI
