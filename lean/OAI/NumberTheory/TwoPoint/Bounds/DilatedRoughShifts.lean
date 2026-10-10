import OAI.NumberTheory.TwoPoint.Bounds.DilatedForwardWindows
import OAI.NumberTheory.TwoPoint.Bounds.QualitativeStrongRoughShifts

namespace OAI

/-! Rough-shift cancellation for the actual factors b(qn), g(qn).
The dilation is unrestricted and its sole cost is the averaged Euler factor. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem qualitative_dilated_rough_shifts (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (P : Finset ℕ) (D : ℕ),
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ q : ℕ, 0 < q → ∀ᶠ Y : ℕ in atTop,
      ∀ b g : ℕ → ℂ, Multiplicative b → OneBounded b → OneBounded g →
      (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
      ∀ (Z : Finset ℕ) (c : ℕ → ℂ),
      (∀ z ∈ Z, D ≤ z ∧ z < D + D ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      (∀ z ∈ Z, ‖c z‖ ≤ 1) →
      ‖weightedRoughShiftAverage (fun n => b (q * n)) (fun n => g (q * n)) Z c h Y‖ ≤
        C * B ^ (-11 / 10 : ℝ) * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  obtain ⟨U, V, hU, hV, hfourier⟩ := hM.qualitative_rough_fourier
  obtain ⟨K, hK, hwindows⟩ := hMRT.dilated_forward_windows hfnp hf C₀ hC₀
  let A := 2 + (2 * (h : ℝ) + 1)
  let T := (2 * (h : ℝ) + 1) * U * V * K
  refine ⟨A + T, by dsimp [A, T]; positivity, ?_⟩
  filter_upwards [hfourier, hwindows, eventually_strong_qualitative_frequency_gap,
    eventually_qualitative_interval_lower, eventually_ge_atTop (Real.exp 1)] with
    B hfour hwin hgap hlower hB
  intro P D hDlower hDupper q hq
  have hDten : 10 ≤ D := hlower D hDlower
  have hDpos : 0 < D := by omega
  have hBpos : 0 < B := (Real.exp_pos 1).trans_le hB
  have hB1 : 1 ≤ B := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hB
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hη : 0 < B ^ (-11 / 10 : ℝ) := Real.rpow_pos_of_pos hBpos _
  let M := smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)
  have hM1 : 1 ≤ M := one_le_smoothReciprocalProduct _
    (fun _ hp => Nat.prime_of_mem_primeFactors hp) (1 / 2) (by norm_num)
  have hM0 : 0 ≤ M := by linarith
  filter_upwards [hwin P D hDlower hDupper q hq,
    eventually_fixed_interval_endpoint D _ hη] with Y hY hend
  intro b g hb hbb hg heq Z c hZ hc
  have hfourZ := hfour D h hDlower hh Z c hZ hc
  have hZinterval : ∀ z ∈ Z, D ≤ z ∧ z < D + D :=
    fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.1⟩
  have hZend : ∀ z ∈ Z, z ≤ 2 * D := by
    intro z hz
    have ht := (hZ z hz).2.1
    omega
  have hr := weighted_rough_shift_parameter_bound (fun n => b (q * n)) (fun n => g (q * n))
    (hbb.mul_argument q hq) (hg.mul_argument q hq) Z c D h Y hDpos hend.1 hZend
    (Real.log B / B ^ (9999 / 10000 : ℝ)) (B ^ (-11 / 10 : ℝ)) U V (K * M)
    (by positivity) hη hU.le hV.le (mul_nonneg hK.le hM0)
    (rough_coefficient_mass_le_one Z c D hDpos hZinterval hc)
    hend.2 hgap hfourZ.1 hfourZ.2 (fun θ => by
      convert hY b hb hbb heq θ using 1
      dsimp [M]
      ring)
  calc
    _ ≤ (A + T * M) * B ^ (-11 / 10 : ℝ) := hr.trans_eq (by dsimp [A, T]; ring)
    _ ≤ (A + T) * B ^ (-11 / 10 : ℝ) * M := by
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hhA := mul_le_mul_of_nonneg_left hM1 hA
      nlinarith [mul_nonneg (sub_nonneg.mpr hhA) hη.le]

end TwoPointCorrelations

end OAI
