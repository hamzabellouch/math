import OAI.NumberTheory.TwoPoint.Halasz.HalaszNearRenormalization
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeightedPrefix
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTDyadicMeanSquare

namespace OAI

/-! Conversion of the centered prefix comparison into the actual dyadic
Fourier energy. The main term is integrated with its exact Cauchy kernel. -/

namespace TwoPointCorrelations

open Finset MeasureTheory

lemma halasz_dyadic_phase (F : ℕ → ℂ) (N : ℕ) (u : ℝ) :
    mrtDyadicPolynomial F N u =
      ∑ n ∈ Ioc N (2 * N), (F n * halaszPowerPhase u n) / (n : ℂ) := by
  unfold mrtDyadicPolynomial mrtExponentialPolynomial
  apply sum_congr rfl
  intro n _
  have he : Complex.exp (((-Real.log (n : ℝ)) * u : ℝ) * Complex.I) =
      halaszPowerPhase u n := by
    unfold halaszPowerPhase
    congr 2
    push_cast
    ring
  rw [he]
  ring

lemma halasz_phase_factor_sq (u : ℝ) :
    (‖(1 : ℂ) + (-u : ℂ) * Complex.I‖⁻¹) ^ 2 = 1 / (1 + u ^ 2) := by
  rw [inv_pow, Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma halasz_near_dyadic_bound (F : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (A E u : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hcenter : ∀ k ∈ Icc N (2 * N), ‖halaszPhaseMean F 0 k‖ ≤ A * k)
    (hnear : ∀ k ∈ Icc N (2 * N),
      ‖halaszPhaseMean F u k -
        (halaszPowerPhase u k / (1 + (-u : ℂ) * Complex.I)) * halaszPhaseMean F 0 k‖ ≤ E * k) :
    ‖mrtDyadicPolynomial F N u‖ ≤
      5 * (‖(1 : ℂ) + (-u : ℂ) * Complex.I‖⁻¹ * A + E) := by
  rw [halasz_dyadic_phase]
  apply mrt_weighted_prefix_bound (fun n => F n * halaszPowerPhase u n) hN
    (by omega) (by omega) (by positivity)
  intro k hk
  change ‖halaszPhaseMean F u k‖ ≤ _
  have hc := hcenter k hk
  have hn := hnear k hk
  let w := halaszPowerPhase u k / (1 + (-u : ℂ) * Complex.I)
  have hw : ‖w‖ = ‖(1 : ℂ) + (-u : ℂ) * Complex.I‖⁻¹ := by
    simp [w]
  calc
    _ = ‖(halaszPhaseMean F u k - w * halaszPhaseMean F 0 k) +
        w * halaszPhaseMean F 0 k‖ := by congr 1; ring
    _ ≤ ‖halaszPhaseMean F u k - w * halaszPhaseMean F 0 k‖ +
        ‖w * halaszPhaseMean F 0 k‖ := norm_add_le _ _
    _ ≤ E * k + ‖w‖ * (A * k) := add_le_add hn
      (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left hc (norm_nonneg w))
    _ = _ := by rw [hw]; ring

lemma halasz_near_dyadic_square (F : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (A E u : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hcenter : ∀ k ∈ Icc N (2 * N), ‖halaszPhaseMean F 0 k‖ ≤ A * k)
    (hnear : ∀ k ∈ Icc N (2 * N),
      ‖halaszPhaseMean F u k -
        (halaszPowerPhase u k / (1 + (-u : ℂ) * Complex.I)) * halaszPhaseMean F 0 k‖ ≤ E * k) :
    ‖mrtDyadicPolynomial F N u‖ ^ 2 ≤ 50 * (A ^ 2 / (1 + u ^ 2) + E ^ 2) := by
  have hb := halasz_near_dyadic_bound F hN A E u hA hE hcenter hnear
  have hs := pow_le_pow_left₀ (norm_nonneg (mrtDyadicPolynomial F N u)) hb 2
  let K := ‖(1 : ℂ) + (-u : ℂ) * Complex.I‖⁻¹
  have he : K ^ 2 = 1 / (1 + u ^ 2) := halasz_phase_factor_sq u
  have hsq : (K * A + E) ^ 2 ≤ 2 * (K ^ 2 * A ^ 2 + E ^ 2) := by
    nlinarith [sq_nonneg (K * A - E)]
  calc
    _ ≤ (5 * (K * A + E)) ^ 2 := hs
    _ ≤ 50 * (K ^ 2 * A ^ 2 + E ^ 2) := by nlinarith
    _ = _ := by rw [he]; ring

/-- Only the squared renormalization error pays for the length of the
near-center frequency interval. -/
theorem halasz_near_dyadic_energy (F : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (A E U : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E) (hU : 0 ≤ U)
    (hcenter : ∀ k ∈ Icc N (2 * N), ‖halaszPhaseMean F 0 k‖ ≤ A * k)
    (hnear : ∀ u ∈ Set.Icc (-U) U, ∀ k ∈ Icc N (2 * N),
      ‖halaszPhaseMean F u k -
        (halaszPowerPhase u k / (1 + (-u : ℂ) * Complex.I)) * halaszPhaseMean F 0 k‖ ≤ E * k) :
    (∫ u in -U..U, ‖mrtDyadicPolynomial F N u‖ ^ 2) ≤
      50 * Real.pi * A ^ 2 + 100 * U * E ^ 2 := by
  have hf : Continuous (fun u => ‖mrtDyadicPolynomial F N u‖ ^ 2) :=
    (mrtExponentialPolynomial_continuous _ _ _).norm.pow 2
  have hg : Continuous (fun u : ℝ => 1 / (1 + u ^ 2)) := by
    fun_prop (disch := intro u; nlinarith [sq_nonneg u])
  have hh := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -U ≤ U)
    (hf.intervalIntegrable _ _)
    (((hg.mul_const (A ^ 2)).add (continuous_const : Continuous (fun _ : ℝ => E ^ 2))).const_mul 50
      |>.intervalIntegrable (-U) U)
    (fun u hu => ?_)
  · simp only [Pi.add_apply] at hh
    have hi : (∫ u in -U..U, 50 * ((1 / (1 + u ^ 2)) * A ^ 2 + E ^ 2)) =
        50 * ((Real.arctan U - Real.arctan (-U)) * A ^ 2 + (2 * U) * E ^ 2) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add ((hg.mul_const (A ^ 2)).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _),
        intervalIntegral.integral_mul_const, integral_one_div_one_add_sq,
        intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    rw [hi] at hh
    have ha := Real.arctan_lt_pi_div_two U
    rw [Real.arctan_neg] at hh
    have hm := mul_le_mul_of_nonneg_right (show 2 * Real.arctan U ≤ Real.pi by linarith) (sq_nonneg A)
    nlinarith
  · convert halasz_near_dyadic_square F hN A E u hA hE hcenter (hnear u hu) using 1
    dsimp only [Pi.add_apply]
    ring

end TwoPointCorrelations

end OAI
