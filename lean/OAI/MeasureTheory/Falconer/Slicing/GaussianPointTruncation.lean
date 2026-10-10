import OAI.MeasureTheory.Falconer.Slicing.GaussianPointCloseBound
import OAI.MeasureTheory.Falconer.Slicing.GaussianBallTruncation

namespace OAI

/-! # Ball-mass deletion for the Gaussian point slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_ball_deletion (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {r ρ : ℝ} {T B : ℝ≥0∞} (hT : 0 < T)
    (hpair : (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 r).prod (gaussianPointSliceMeasure μ p.1 p.2 r))
        {z | dist z.1 z.2 < ρ} ∂(gaussianRows d h).prod volume) ≤ B) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      gaussianPointSliceMeasure μ p.1 p.2 r
        {x | T < gaussianPointSliceMeasure μ p.1 p.2 r (ball x ρ)}
          ∂(gaussianRows d h).prod volume) ≤ T⁻¹*B := by
  calc
    _ ≤ ∫⁻ p : (Fin h → Space d) × Space h, T⁻¹*
        ((gaussianPointSliceMeasure μ p.1 p.2 r).prod (gaussianPointSliceMeasure μ p.1 p.2 r))
          {z | dist z.1 z.2 < ρ} ∂(gaussianRows d h).prod volume :=
      lintegral_mono (fun p => excessive_ball_mass (gaussianPointSliceMeasure μ p.1 p.2 r) ρ hT.ne')
    _ = T⁻¹*∫⁻ p : (Fin h → Space d) × Space h,
        ((gaussianPointSliceMeasure μ p.1 p.2 r).prod (gaussianPointSliceMeasure μ p.1 p.2 r))
          {z | dist z.1 z.2 < ρ} ∂(gaussianRows d h).prod volume :=
      lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hT.ne')
    _ ≤ _ := mul_le_mul_right hpair _

theorem gaussian_point_good_ball (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (A : Fin h → Space d) (z : Space h) (r ρ : ℝ) (T : ℝ≥0∞) (a : Space d) :
    ((gaussianPointSliceMeasure μ A z r).restrict
      {x | gaussianPointSliceMeasure μ A z r (ball x (2*ρ)) ≤ T}) (ball a ρ) ≤ T :=
  restricted_good_ball_bound (gaussianPointSliceMeasure μ A z r) ρ T a

end Falconer

end OAI
