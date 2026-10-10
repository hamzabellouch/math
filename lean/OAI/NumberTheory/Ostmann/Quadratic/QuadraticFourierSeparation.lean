import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGaussBilinear
import OAI.NumberTheory.Ostmann.QuadraticCenter.RealQuadraticPhase

namespace OAI

/-! # Exact logarithmic Fourier separation of a smooth pair weight -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

 theorem quadratic_schwartz_inversion (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    f x = ∫ u : ℝ, realAdditivePhase (u * x) * 𝓕 f u := by
  have hi := congrArg (fun g : 𝓢(ℝ, ℂ) => g x)
    (show (𝓕⁻ (𝓕 f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = f from
      FourierTransform.fourierInv_fourier_eq f)
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg,
    Real.fourier_real_eq_integral_exp_smul] at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards with u
  congr 1
  unfold realAdditivePhase
  congr 1
  push_cast
  ring

 theorem quadratic_log_pair_integrable (f : 𝓢(ℝ, ℂ)) (c : ℂ) (s t : ℕ) :
    Integrable (fun u : ℝ => c * realAdditivePhase (u * Real.log s) *
      realAdditivePhase (u * Real.log t) * 𝓕 f u) := by
  apply (((𝓕 f : 𝓢(ℝ, ℂ)).integrable.norm).const_mul ‖c‖).mono'
    (by unfold realAdditivePhase; fun_prop)
  filter_upwards with u
  simp only [norm_mul, norm_realAdditivePhase, mul_one, le_refl]

 theorem quadratic_finite_log_separation (f : 𝓢(ℝ, ℂ)) (S T : Finset ℕ)
    (c : ℕ → ℕ → ℂ) :
    (∑ s ∈ S, ∑ t ∈ T, c s t * f (Real.log s + Real.log t)) =
      ∫ u : ℝ, 𝓕 f u * ∑ s ∈ S, ∑ t ∈ T,
        c s t * realAdditivePhase (u * Real.log s) *
          realAdditivePhase (u * Real.log t) := by
  have ht (s t : ℕ) : c s t * f (Real.log s + Real.log t) =
      ∫ u : ℝ, c s t * realAdditivePhase (u * Real.log s) *
        realAdditivePhase (u * Real.log t) * 𝓕 f u := by
    rw [quadratic_schwartz_inversion, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    rw [mul_add, realAdditivePhase_add]
    ring
  simp_rw [ht]
  calc
    _ = ∑ s ∈ S, ∫ u : ℝ, ∑ t ∈ T,
        c s t * realAdditivePhase (u * Real.log s) *
          realAdditivePhase (u * Real.log t) * 𝓕 f u := by
      apply Finset.sum_congr rfl
      intro s _
      exact (integral_finsetSum T
        (fun t _ => quadratic_log_pair_integrable f (c s t) s t)).symm
    _ = ∫ u : ℝ, ∑ s ∈ S, ∑ t ∈ T,
        c s t * realAdditivePhase (u * Real.log s) *
          realAdditivePhase (u * Real.log t) * 𝓕 f u :=
      (integral_finsetSum S (fun s _ =>
        integrable_finsetSum T (fun t _ => quadratic_log_pair_integrable f (c s t) s t))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring

noncomputable def quadraticLogModulate (u : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * realAdditivePhase (u * Real.log n)

 theorem quadraticLogModulate_norm (u : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    ‖quadraticLogModulate u a n‖ = ‖a n‖ := by
  rw [quadraticLogModulate, norm_mul, norm_realAdditivePhase, mul_one]

 theorem quadraticSieveEnergy_logModulate (N : ℕ) (u : ℝ) (a : ℕ → ℂ) :
    quadraticSieveEnergy N (quadraticLogModulate u a) = quadraticSieveEnergy N a := by
  apply Finset.sum_congr rfl
  intro n _
  rw [quadraticLogModulate_norm]

 theorem quadraticDivisorMoment_logModulate (N : ℕ) (u : ℝ) (a : ℕ → ℂ) :
    quadraticDivisorMoment N (quadraticLogModulate u a) = quadraticDivisorMoment N a := by
  apply Finset.sum_congr rfl
  intro n _
  rw [quadraticLogModulate_norm]

end Ostmann

end OAI
