import OAI.Geometry.RCD.Heat.CanonicalGaussianUpper
import OAI.Geometry.RCD.Heat.KernelGaussianDifference

namespace OAI

/-! # Gaussian finite differences for the canonical heat kernel

The upper Gaussian bound and actual reverse Poincaré now supply the
finite-difference estimate without any Gaussian premise.
-/

open Set Metric MeasureTheory TopologicalSpace
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_upper_five :
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧ ∀ t, 0 < t → ∀ x y,
      hX.canonicalHeatKernel hn p t x y ≤ C/(hausdorff n X).real (ball y (Real.sqrt t))*
        Real.exp (-dist x y^2/(5*t)+B*t) := by
  obtain ⟨C,B,hC,hB,h⟩ := hX.canonicalHeatKernel_gaussian_upper hn p (show (0:ℝ) < 1/2 by norm_num)
  refine ⟨C,B,hC,hB,?_⟩
  intro t ht x y
  apply (h t ht x y).trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hC.le ENNReal.toReal_nonneg)
  apply Real.exp_le_exp.mpr
  have hpos : dist x y^2/(5*t) ≤ dist x y^2/((4+(1/2:ℝ))*t) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _)
    · positivity
    · nlinarith
  have hd : -dist x y^2/((4+(1/2:ℝ))*t) ≤ -dist x y^2/(5*t) := by
    simpa only [neg_div] using neg_le_neg hpos
  linarith

theorem canonicalHeatKernel_gaussian_difference :
    HasGaussianHeatDifferenceBounds (hausdorff n X) (hX.canonicalHeatKernel hn p) := by
  obtain ⟨C,B,hC,hB,hupper⟩ := hX.canonicalHeatKernel_upper_five hn p
  exact hX.gaussianHeatDifferenceBounds_of_upper hn
    (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) hC hB hupper

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
