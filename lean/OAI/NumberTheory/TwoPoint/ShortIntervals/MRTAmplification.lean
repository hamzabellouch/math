import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMixedPolynomial
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRestrictedEnergy

namespace OAI

/-! Amplification on the multiscale classes where a preceding short-prime
polynomial is large. The inserted power is estimated by the actual mixed
prime/cofactor moment, not by an assumed large-value proposition. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_amplified_energy (Q R : ℝ → ℂ) (hQ : Continuous Q) (hR : Continuous R)
    (r : ℕ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤ ‖Q t‖) :
    (∫ t in E, ‖R t‖ ^ 2) ≤
      (∫ t in -T..T, ‖Q t ^ r * R t‖ ^ 2) / V ^ (2 * r) := by
  have hprod : Continuous (fun t => Q t ^ r * R t) := (hQ.pow r).mul hR
  have hi := mrt_continuous_square_integrable hprod hT hE
  apply (le_div_iff₀ (pow_pos hV _)).mpr
  calc
    _ = ∫ t in E, V ^ (2 * r) * ‖R t‖ ^ 2 := by
      rw [integral_const_mul]
      ring
    _ ≤ ∫ t in E, ‖Q t ^ r * R t‖ ^ 2 := by
      apply setIntegral_mono_of_nonneg (fun _ _ => by positivity) _ hi
      intro t ht
      rw [norm_mul, norm_pow, mul_pow, ← pow_mul, Nat.mul_comm r 2]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hV.le (hlarge t ht) _) (sq_nonneg _)
    _ ≤ _ := mrt_restricted_square_le_interval hprod hT hE

theorem mrt_large_prime_class_cofactor_energy (P M : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hM : ∀ m ∈ M, 0 < m)
    (a b : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1) (hb : ∀ m ∈ M, ‖b m‖ ≤ 1)
    (r : ℕ) {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    (hsupport : ∀ v ∈ Fintype.piFinset (fun _ : Fin r => P), ∀ m ∈ M,
      L < (∏ i, v i) * m ∧ (∏ i, v i) * m ≤ U)
    {T V : ℝ} (hT : 0 < T) (hV : 0 < V)
    {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤
      ‖mrtExponentialPolynomial P (fun p => a p / (p : ℂ))
        (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in E, ‖mrtExponentialPolynomial M (fun m => b m / (m : ℂ))
      (fun m => -Real.log (m : ℝ)) t‖ ^ 2) ≤
      (16 * Real.exp 1 * ((T + U) / (L : ℝ)) * (r.factorial : ℝ) ^ 2 *
        (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3) / V ^ (2 * r) := by
  apply (mrt_amplified_energy _ _
    (mrtExponentialPolynomial_continuous _ _ _)
    (mrtExponentialPolynomial_continuous _ _ _) r hT.le hV hE hlarge).trans
  exact div_le_div_of_nonneg_right
    (mrt_mixed_prime_cofactor_mean_square P M hP hM a b ha hb r hL hLU hsupport hT)
    (pow_nonneg hV.le _)

end TwoPointCorrelations

end OAI
