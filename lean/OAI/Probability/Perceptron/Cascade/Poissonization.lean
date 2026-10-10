import Mathlib
import OAI.Probability.Perceptron.Variational.DensityDerivative

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma poisson_abs_count_difference (r : ℝ≥0) (M : ℕ) :
    (∫ j : ℕ, |(j:ℝ)-(M:ℝ)| ∂poissonMeasure r) ≤ Real.sqrt r+|(r:ℝ)-(M:ℝ)| := by
  have hi := (poisson_nat_memLp r).integrable (by norm_num)
  have hc := integral_centered_abs_le_sqrt_variance (poissonMeasure r) (poisson_nat_memLp r)
  rw [poisson_nat_mean,poisson_nat_variance] at hc
  calc
    _ ≤ ∫ j : ℕ, |(j:ℝ)-(r:ℝ)|+|(r:ℝ)-(M:ℝ)| ∂poissonMeasure r := by
      apply integral_mono (hi.sub (integrable_const _)).abs
        ((hi.sub (integrable_const _)).abs.add (integrable_const _))
      intro j
      exact abs_sub_le _ _ _
    _ = (∫ j : ℕ, |(j:ℝ)-(r:ℝ)| ∂poissonMeasure r)+|(r:ℝ)-(M:ℝ)| := by
      rw [integral_add (f := fun j : ℕ => |(j:ℝ)-(r:ℝ)|)
        (g := fun _ : ℕ => |(r:ℝ)-(M:ℝ)|) (hi.sub (integrable_const _)).abs (integrable_const _)]
      simp
    _ ≤ _ := add_le_add hc le_rfl

lemma poisson_bounded_increment_mean_compare (r : ℝ≥0) {F : ℕ→ℝ} {C : ℝ}
    (hC : 0≤C) (hF : ∀ m, |F (m+1)-F m|≤C) (M : ℕ) :
    |(∫ j, F j ∂poissonMeasure r)-F M|≤C*(Real.sqrt r+|(r:ℝ)-(M:ℝ)|) := by
  have hi := (poisson_bounded_increment_memLp r hC hF).integrable (by norm_num)
  have hj := (poisson_nat_memLp r).integrable (by norm_num)
  calc
    _ = |∫ j, F j-F M ∂poissonMeasure r| := by rw [integral_sub hi (integrable_const _)]; simp
    _ ≤ ∫ j, |F j-F M| ∂poissonMeasure r := abs_integral_le_integral_abs
    _ ≤ ∫ j : ℕ, C*|(j:ℝ)-(M:ℝ)| ∂poissonMeasure r :=
      integral_mono (hi.sub (integrable_const _)).abs
        ((hj.sub (integrable_const _)).abs.const_mul C)
        (fun j => nat_bounded_increment_difference hC hF j M)
    _ ≤ _ := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left (poisson_abs_count_difference r M) hC

lemma sourceExpectedPressure_fixed_count_compare (n k M : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    |sourceExpectedPressure n k f p d h z t u-(1/(n+1:ℕ))*sourceCountExpectedLog n k f p d h z u M| ≤
      ‖f‖/(n+1:ℕ)*(Real.sqrt ((n+1:ℕ)*(t:ℝ))+|((n+1:ℕ)*(t:ℝ))-(M:ℝ)|) := by
  rw [sourceExpectedPressure_poissonMean n k f p d h z u hz hz0 hz1]
  have hF := sourceCountExpectedLog_increment n k f p d h z u hz hz0 hz1
  have H := poisson_bounded_increment_mean_compare ((n+1:ℕ)*t) (norm_nonneg f) hF M
  rw [← poissonRealMean_eq_integral (norm_nonneg f) hF] at H
  simp only [NNReal.coe_mul,NNReal.coe_natCast] at H
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤1/(n+1:ℕ))]
  calc
    _ ≤ (1/(n+1:ℕ))*(‖f‖*(Real.sqrt ((n+1:ℕ)*(t:ℝ))+|((n+1:ℕ)*(t:ℝ))-(M:ℝ)|)) :=
      mul_le_mul_of_nonneg_left H (by positivity)
    _ = _ := by ring

lemma sourceExpectedPressure_floor_count_compare (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    |sourceExpectedPressure n k f p d h z t u-
      (1/(n+1:ℕ))*sourceCountExpectedLog n k f p d h z u ⌊(n+1:ℕ)*(t:ℝ)⌋₊| ≤
      ‖f‖/(n+1:ℕ)*(Real.sqrt ((n+1:ℕ)*(t:ℝ))+1) := by
  apply (sourceExpectedPressure_fixed_count_compare n k _ f p d h z u hz hz0 hz1 t).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  rw [abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le (by positivity)))]
  linarith [Nat.lt_floor_add_one ((n+1:ℕ)*(t:ℝ))]

end SphericalPerceptronFreeEnergy
end

end OAI
