import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalRemoval

namespace OAI

/-! Restore the full coefficient function after estimating its literal
prime-band typical short sum. -/

namespace TwoPointCorrelations

open Finset MeasureTheory Set
open scoped Classical

lemma halasz_short_square_integrable (F : ℕ → ℂ) {N H : ℕ} (hHN : H ≤ N) :
    IntervalIntegrable (fun x => ‖shortExponentialSum F H 0 x‖^2)
      volume (N:ℝ) (2*N) := by
  have hh := mrt_interval_sum_sq_intervalIntegrable (Finset.Ioc N (4*N)) F
    (x := id) (h := fun _ => (H:ℝ)) measurable_id measurable_const (N:ℝ) (2*N)
  apply hh.congr
  intro x hx
  rw [uIoc_of_le (by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)] : (N:ℝ) ≤ 2*N)] at hx
  have he := mrt_finite_window_eq_short_sum F hHN ⟨hx.1.le, hx.2⟩ 0
  simpa only [Function.id_def, additiveCharacter, mul_zero, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, mul_one] using congrArg (fun z : ℂ => ‖z‖^2) he

theorem halasz_short_transfer {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    {N H : ℕ} (hH : 0 < H) (hHN : H ≤ N)
    {δ ε : ℝ}
    (hδ : ∀ k ∈ ({N, 2*N} : Finset ℕ),
      (((Finset.Ioc k (2*k)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / k ≤ δ)
    (htyp : (∫ x in (N:ℝ)..(2*N),
        ‖shortExponentialSum (mrtTypicalCoefficient J P F) H 0 x‖^2) /
          ((N:ℝ)*(H:ℝ)^2) ≤ ε) :
    (∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum F H 0 x‖^2) /
      ((N:ℝ)*(H:ℝ)^2) ≤
        2*ε + (279936/(2*Real.pi))*(448*Real.exp 1*δ) := by
  let G := mrtTypicalCoefficient J P F
  have hI := halasz_short_square_integrable F hHN
  have hJ := halasz_short_square_integrable G hHN
  have hD := halasz_short_square_integrable (fun n => F n-G n) hHN
  simp_rw [halasz_short_sum_sub] at hD
  have hm := intervalIntegral.integral_mono_on (μ := volume)
    (by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)] : (N:ℝ) ≤ 2*N) hI
    ((hD.const_mul 2).add (hJ.const_mul 2)) (fun x _ => by
      have he := norm_add_le
        (shortExponentialSum F H 0 x - shortExponentialSum G H 0 x)
        (shortExponentialSum G H 0 x)
      rw [sub_add_cancel] at he
      nlinarith [sq_nonneg (‖shortExponentialSum F H 0 x - shortExponentialSum G H 0 x‖ -
        ‖shortExponentialSum G H 0 x‖), norm_nonneg (shortExponentialSum F H 0 x)])
  rw [intervalIntegral.integral_add (hD.const_mul 2) (hJ.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hm
  have hn := div_le_div_of_nonneg_right hm
    (show 0 ≤ (N:ℝ)*(H:ℝ)^2 by positivity)
  have herr := halasz_typical_short_error J P F hF hH hHN hδ
  calc
    _ ≤ 2*((∫ x in (N:ℝ)..(2*N),
          ‖shortExponentialSum F H 0 x-shortExponentialSum G H 0 x‖^2) /
          ((N:ℝ)*(H:ℝ)^2)) +
        2*((∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum G H 0 x‖^2) /
          ((N:ℝ)*(H:ℝ)^2)) := by convert hn using 1; ring
    _ ≤ 2*((139968/(2*Real.pi))*(448*Real.exp 1*δ)) + 2*ε :=
      add_le_add (mul_le_mul_of_nonneg_left herr (by norm_num))
        (mul_le_mul_of_nonneg_left htyp (by norm_num))
    _ = _ := by ring

end TwoPointCorrelations

end OAI
