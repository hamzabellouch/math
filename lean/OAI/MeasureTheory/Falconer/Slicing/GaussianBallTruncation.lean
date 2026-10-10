import OAI.MeasureTheory.Falconer.Slicing.GaussianCloseBound
import OAI.MeasureTheory.Falconer.Geometry.BallTruncation

namespace OAI

/-! # Ball-mass deletion for the Gaussian direction slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_direction_ball_deletion (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {r ρ : ℝ} {T B : ℝ≥0∞} (hT : 0 < T)
    (hpair : (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A r).prod (gaussianDirectionSliceMeasure ν A r))
        {z | dist z.1 z.2 < ρ} ∂gaussianRows d h) ≤ B) :
    (∫⁻ A : Fin h → Space d,
      gaussianDirectionSliceMeasure ν A r
        {w | T < gaussianDirectionSliceMeasure ν A r (ball w ρ)} ∂gaussianRows d h) ≤ T⁻¹*B := by
  calc
    _ ≤ ∫⁻ A : Fin h → Space d, T⁻¹*
        ((gaussianDirectionSliceMeasure ν A r).prod (gaussianDirectionSliceMeasure ν A r))
          {z | dist z.1 z.2 < ρ} ∂gaussianRows d h :=
      lintegral_mono (fun A => excessive_ball_mass (gaussianDirectionSliceMeasure ν A r) ρ hT.ne')
    _ = T⁻¹*∫⁻ A : Fin h → Space d,
        ((gaussianDirectionSliceMeasure ν A r).prod (gaussianDirectionSliceMeasure ν A r))
          {z | dist z.1 z.2 < ρ} ∂gaussianRows d h :=
      lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hT.ne')
    _ ≤ _ := mul_le_mul_right hpair _

theorem gaussian_direction_good_ball (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    (A : Fin h → Space d) (r ρ : ℝ) (T : ℝ≥0∞) (a : Sphere d) :
    ((gaussianDirectionSliceMeasure ν A r).restrict
      {w | gaussianDirectionSliceMeasure ν A r (ball w (2*ρ)) ≤ T}) (ball a ρ) ≤ T :=
  restricted_good_ball_bound (gaussianDirectionSliceMeasure ν A r) ρ T a

end Falconer

end OAI
