import OAI.NumberTheory.TwoPoint.Bounds.QualitativeStrongRoughShifts
import OAI.NumberTheory.TwoPoint.Bounds.QualitativeRightShifts

namespace OAI

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

/-- The second-factor counterpart of `qualitative_rough_shifts`, with the
same exponent and uniformity in finite prime changes. -/
theorem qualitative_strong_rough_shifts_right (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (P : Finset ℕ) (D : ℕ),
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ᶠ Y : ℕ in atTop, ∀ b g : ℕ → ℂ,
      OneBounded b → Multiplicative g → OneBounded g →
      (∀ p, Nat.Prime p → p ∉ P → g p = f p) →
      ∀ (l : ℕ) [NeZero l] (a : ZMod l) (Z : Finset ℕ) (c : ℕ → ℂ),
      (∀ z ∈ Z, D ≤ z ∧ z < D + D ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      (∀ z ∈ Z, ‖c z‖ ≤ 1) →
      ‖weightedRoughShiftAverage (progressionSequence b l a) g Z c h Y‖ ≤
        C * B ^ (-11 / 10 : ℝ) := by
  obtain ⟨U, V, hU, hV, hfourier⟩ := hM.qualitative_rough_fourier
  obtain ⟨K, hK, hwindows⟩ := hMRT.qualitative_square_window_scale hfnp hf
    (C₀ + (2 * (h : ℝ) + 1)) (by
      have ht : (0 : ℝ) ≤ h := Nat.cast_nonneg h
      linarith only [hC₀, ht])
  let C := 2 + (2 * (h : ℝ) + 1) + (2 * (h : ℝ) + 1) * U * V * K
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hfourier, hwindows, eventually_strong_qualitative_frequency_gap,
    eventually_qualitative_interval_lower, eventually_ge_atTop (Real.exp 1)] with
    B hfour hwin hgap hlower hB
  intro P D hDlower hDupper
  have hDten : 10 ≤ D := hlower D hDlower
  have hDpos : 0 < D := by omega
  have hB₁ : 1 ≤ B := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hB
  have hBpos : 0 < B := zero_lt_one.trans_le hB₁
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB₁
  have hη : 0 < B ^ (-11 / 10 : ℝ) := Real.rpow_pos_of_pos hBpos _
  let Q := (2 * h + 1) * D
  have hDQ : D ≤ Q := Nat.le_mul_of_pos_left D (by omega)
  have hQten : 10 ≤ Q := hDten.trans hDQ
  have hQlower : (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ Q :=
    hDlower.trans (by exact_mod_cast hDQ)
  have hQupper : (Q : ℝ) ≤ Real.exp ((C₀ + (2 * (h : ℝ) + 1)) * B ^ (2 : ℕ)) :=
    long_window_exp_bound (B ^ (2 : ℕ)) C₀ D h (by nlinarith) hDupper
  filter_upwards [hwin P Q hQten hQlower hQupper,
    eventually_fixed_interval_endpoint D _ hη] with Y hy hend
  intro b g hbounded hmult hg heq l _ a Z c hZ hc
  have hfourZ := hfour D h hDlower hh Z c hZ hc
  have hZinterval : ∀ z ∈ Z, D ≤ z ∧ z < D + D :=
    fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.1⟩
  have hZend : ∀ z ∈ Z, z ≤ 2 * D := by
    intro z hz
    have ht := (hZ z hz).2.1
    omega
  apply weighted_rough_shift_parameter_bound_right (progressionSequence b l a) g
    (hbounded.progressionSequence l a) hg Z c D h Y hDpos hend.1 hZend
    (Real.log B / B ^ (9999 / 10000 : ℝ)) (B ^ (-11 / 10 : ℝ)) U V K
    (by positivity) hη hU.le hV.le hK.le
    (rough_coefficient_mass_le_one Z c D hDpos hZinterval hc)
    hend.2 hgap hfourZ.1 hfourZ.2
  intro θ
  have hG := hy g hmult hg heq 1 (0 : ZMod 1) (-θ)
  simp only [progressionSequence_mod_one] at hG
  simp_rw [backwardWindowPolynomial_eq_forward_neg]
  convert hG using 1
  dsimp [Q]
  push_cast
  ring

end TwoPointCorrelations

end OAI
