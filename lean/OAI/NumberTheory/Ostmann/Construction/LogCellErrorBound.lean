import OAI.NumberTheory.Ostmann.Construction.LogCellAbel

namespace OAI

open MeasureTheory
namespace Ostmann.Construction

lemma smooth_prime_sum_error_bound (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (f g : ℝ → ℝ) (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (g t) t)
    (hg : ContinuousOn g (Set.Icc a b)) (hfa : f a = 0) (hfb : f b = 0)
    (ε : ℝ) (hθ : ∀ t ∈ Set.Icc a b, |Chebyshev.theta t-t| ≤ ε*t) :
    |(∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with n.Prime, f n*Real.log n) -
      (∫ t in a..b, f t)| ≤ ε*(∫ t in a..b, t*|g t|) := by
  rw [smooth_prime_sum_error_identity a b ha hab f g hf hg hfa hfb, abs_neg]
  have hgc : ContinuousOn g (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  have hi : IntervalIntegrable (fun t => |g t*(Chebyshev.theta t-t)|) volume a b :=
    ((Chebyshev.theta_mono.intervalIntegrable.sub (continuous_id.intervalIntegrable a b)).continuousOn_mul hgc).abs
  have hr : IntervalIntegrable (fun t => ε*(t*|g t|)) volume a b :=
    (continuousOn_const.mul (continuous_id.continuousOn.mul hgc.abs)).intervalIntegrable
  calc
    _ ≤ ∫ t in a..b, |g t*(Chebyshev.theta t-t)| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, ε*(t*|g t|) := by
      apply intervalIntegral.integral_mono_on hab hi hr
      intro t ht
      rw [abs_mul]
      calc
        _ ≤ |g t| *(ε*t) := mul_le_mul_of_nonneg_left (hθ t ht) (abs_nonneg _)
        _ = _ := by ring
    _ = _ := intervalIntegral.integral_const_mul _ _

end Ostmann.Construction

end OAI
