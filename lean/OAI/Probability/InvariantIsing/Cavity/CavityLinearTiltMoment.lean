import OAI.Probability.InvariantIsing.Cavity.CavityLogCap
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianEnvelope

namespace OAI

/-! Moments after the remaining linear tilt can be bounded using only
one-replica Gaussian moments, by Jensen and the elementary product bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_linear_tilt_moment_bound {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (V f : X → ℝ)
    (hV : Integrable V ν) (he : Integrable (fun x => Real.exp (V x)) ν)
    (heNeg : Integrable (fun x => Real.exp (-V x)) ν) (hf0 : ∀ x, 0 ≤ f x)
    (hfe : Integrable (fun x => f x * Real.exp (V x)) ν)
    (hfe2 : Integrable (fun x => (f x * Real.exp (V x))^2) ν)
    (heNeg2 : Integrable (fun x => Real.exp (-V x)^2) ν) :
    (∫ x, f x ∂ν.tilted V) ≤
      ((∫ x, (f x * Real.exp (V x))^2 ∂ν) + (∫ x, Real.exp (-V x)^2 ∂ν)) / 2 := by
  have hJ := partition_inv_pow_le (ν := ν) (H := V) 1 hV he (by
    simpa only [Nat.cast_one, neg_mul, one_mul] using heNeg)
  simp only [pow_one, Nat.cast_one, neg_mul, one_mul] at hJ
  have hA0 : 0 ≤ ∫ x, f x * Real.exp (V x) ∂ν := integral_nonneg
    (fun x => mul_nonneg (hf0 x) (Real.exp_pos _).le)
  have hA := (convexOn_pow 2 (𝕜 := ℝ)).map_integral_le (by fun_prop) isClosed_Ici
    (ae_of_all _ (fun x => mul_nonneg (hf0 x) (Real.exp_pos _).le)) hfe hfe2
  have hB := (convexOn_pow 2 (𝕜 := ℝ)).map_integral_le (by fun_prop) isClosed_Ici
    (ae_of_all _ (fun x => (Real.exp_pos (-V x)).le)) heNeg heNeg2
  have hbound := mul_le_mul_of_nonneg_left hJ hA0
  rw [integral_tilted_eq_div]
  have hswap : (∫ x, Real.exp (V x) * f x ∂ν) = ∫ x, f x * Real.exp (V x) ∂ν := by
    apply integral_congr_ae
    exact ae_of_all _ (fun x => mul_comm _ _)
  rw [hswap, div_eq_mul_inv]
  nlinarith [sq_nonneg ((∫ x, f x * Real.exp (V x) ∂ν) - ∫ x, Real.exp (-V x) ∂ν)]

end InvariantIsing

end

end OAI
