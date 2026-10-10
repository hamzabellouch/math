import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Compactness.L1VelocityTranslationApproximation
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedGainCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicInitialEntropyLimit

namespace OAI

section

/-! # Vanishing initial positive-difference error along arbitrary late subsequences -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness TransportPrimitive

theorem initialApproximation_comparison_L1 {f : Density} (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable f)
    {I J : ℕ → ℕ} (hI : Tendsto I atTop atTop) (hJ : Tendsto J atTop atTop)
    {ν : Measure Phase} (hν : ν ≤ volume) :
    Tendsto (fun n => eLpNorm (fun p =>
      |positiveDifference (initialApproximation ((I n:ℝ)+1) f p)
        (initialApproximation ((J n:ℝ)+1) f p)|) 1 ν) atTop (𝓝 0) := by
  have ht := strongL1_sub_of_common_limit
    ((initialApproximation_norm_tendsto hfm hf hi).comp hI)
    ((initialApproximation_norm_tendsto hfm hf hi).comp hJ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  apply le_trans _ (eLpNorm_mono_measure _ hν)
  have hm : Measurable (fun p => |positiveDifference
      (initialApproximation ((I n:ℝ)+1) f p) (initialApproximation ((J n:ℝ)+1) f p)|) :=
    (((initialApproximation_measurable _ hfm).sub (initialApproximation_measurable _ hfm)).div
      ((measurable_const.add (initialApproximation_measurable _ hfm)).add
        (initialApproximation_measurable _ hfm))).abs
  apply eLpNorm_mono hm.aestronglyMeasurable
  intro p
  simp only [Real.norm_eq_abs,abs_abs]
  exact normalized_difference_abs_le
    (initialApproximation_bounds (by positivity : 0 ≤ (I n:ℝ)+1) f p).1
    (initialApproximation_bounds (by positivity : 0 ≤ (J n:ℝ)+1) f p).1

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The initial approximation converges in the positive comparison metric -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness TransportPrimitive

theorem initialApproximation_linear_comparison_L1 {f : Density} (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable f)
    {I : ℕ → ℕ} (hI : Tendsto I atTop atTop)
    {ν : Measure Phase} (hν : ν ≤ volume) :
    Tendsto (fun n => eLpNorm (fun p =>
      |positiveDifference (initialApproximation ((I n:ℝ)+1) f p) (f p)|) 1 ν)
      atTop (𝓝 0) := by
  have ht := (initialApproximation_norm_tendsto hfm hf hi).comp hI
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  apply le_trans _ (eLpNorm_mono_measure _ hν)
  have hm : Measurable (fun p => |positiveDifference
      (initialApproximation ((I n:ℝ)+1) f p) (f p)|) :=
    (((initialApproximation_measurable _ hfm).sub hfm).div
      ((measurable_const.add (initialApproximation_measurable _ hfm)).add hfm)).abs
  apply eLpNorm_mono hm.aestronglyMeasurable
  intro p
  simp only [Real.norm_eq_abs,abs_abs]
  exact normalized_difference_abs_le
    (initialApproximation_bounds (by positivity : 0 ≤ (I n:ℝ)+1) f p).1 (hf p)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
