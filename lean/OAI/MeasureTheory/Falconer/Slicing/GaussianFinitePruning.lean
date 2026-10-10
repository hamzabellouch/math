import OAI.MeasureTheory.Falconer.Incidence.FiniteBallPruning
import OAI.MeasureTheory.Falconer.Slicing.GaussianRestrictedMass
import OAI.MeasureTheory.Falconer.Slicing.GaussianPointTruncation

namespace OAI

/-! # Simultaneous Gaussian slice pruning at the required finite scales -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_direction_finite_ball_deletion
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (δ : ℝ)
    (r : ι → ℝ) (T C : ι → ℝ≥0∞) (hT : ∀ i, 0 < T i)
    (hp : ∀ i, (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows d h) ≤ C i) :
    (∫⁻ A : Fin h → Space d, gaussianDirectionSliceMeasure ν A δ
      (finiteBallGood (gaussianDirectionSliceMeasure ν A δ) r T)ᶜ ∂gaussianRows d h) ≤
        ∑ i, (T i)⁻¹*C i := by
  classical
  calc
    _ ≤ ∫⁻ A : Fin h → Space d, ∑ i,
        gaussianDirectionSliceMeasure ν A δ
          {w | T i < gaussianDirectionSliceMeasure ν A δ (ball w (2*r i))}
          ∂gaussianRows d h :=
      lintegral_mono (fun A => finiteBallGood_compl_mass _ r T)
    _ = ∑ i, ∫⁻ A : Fin h → Space d, gaussianDirectionSliceMeasure ν A δ
        {w | T i < gaussianDirectionSliceMeasure ν A δ (ball w (2*r i))}
        ∂gaussianRows d h := lintegral_finsetSum _
          (fun i _ => gaussian_direction_bad_ball_mass_measurable ν δ (2*r i) (T i))
    _ ≤ _ := Finset.sum_le_sum (fun i _ => gaussian_direction_ball_deletion ν (hT i) (hp i))

theorem gaussian_point_finite_ball_deletion
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (δ : ℝ)
    (r : ι → ℝ) (T C : ι → ℝ≥0∞) (hT : ∀ i, 0 < T i)
    (hp : ∀ i, (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows d h).prod volume) ≤ C i) :
    (∫⁻ p : (Fin h → Space d) × Space h, gaussianPointSliceMeasure μ p.1 p.2 δ
      (finiteBallGood (gaussianPointSliceMeasure μ p.1 p.2 δ) r T)ᶜ
        ∂(gaussianRows d h).prod volume) ≤ ∑ i, (T i)⁻¹*C i := by
  classical
  calc
    _ ≤ ∫⁻ p : (Fin h → Space d) × Space h, ∑ i,
        gaussianPointSliceMeasure μ p.1 p.2 δ
          {x | T i < gaussianPointSliceMeasure μ p.1 p.2 δ (ball x (2*r i))}
          ∂(gaussianRows d h).prod volume :=
      lintegral_mono (fun p => finiteBallGood_compl_mass _ r T)
    _ = ∑ i, ∫⁻ p : (Fin h → Space d) × Space h, gaussianPointSliceMeasure μ p.1 p.2 δ
        {x | T i < gaussianPointSliceMeasure μ p.1 p.2 δ (ball x (2*r i))}
        ∂(gaussianRows d h).prod volume := lintegral_finsetSum _
          (fun i _ => gaussian_point_bad_ball_mass_measurable μ δ (2*r i) (T i))
    _ ≤ _ := Finset.sum_le_sum (fun i _ => gaussian_point_ball_deletion μ (hT i) (hp i))

end Falconer

end OAI
