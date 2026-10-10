import OAI.Geometry.RCD.Sobolev.DistancePoissonErrors
import OAI.Geometry.RCD.Sobolev.PoissonSourceLocalization

namespace OAI

/-! # Source and energy data retained by the actual compact extensions -/

open Set Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {Q : QuadraticCheegerEnergy μ}
  {n : ℕ} {κ B J C : ℝ} {p : ℕ → X} {r : ℕ → ℝ} {hr : ∀ k, 0<r k}
  (F : DistancePoissonFamily μ Q n κ B J C p r hr)

theorem DistancePoissonFamily.extension_local_data (k : ℕ) (u : SobolevSpace μ Q)
    (hu : SobolevSpace.toLp μ Q u =ᵐ[μ.restrict (ball (p k) (r k/16))]
      SobolevSpace.toLp μ Q (F.replacement k)) :
    (∀ (ψ : SobolevSpace μ Q) (v : X → ℝ) (L : ℝ≥0),
      LipschitzWith L v → HasCompactSupport v → tsupport v ⊆ ball (p k) (r k/16) →
      SobolevSpace.toLp μ Q ψ =ᵐ[μ] v →
      energyForm μ Q (F.datum k) ψ+((n:ℝ)+κ*(4*r k)^2)*(∫ x in ball (p k) (r k/16), v x ∂μ)=
        ∫ x, v x ∂F.source k) ∧
    ((fun x => (1/2:ℝ)*localGamma μ Q (F.datum k) (F.datum k) x)
      =ᵐ[μ.restrict (ball (p k) (r k/16))] SobolevSpace.toLp μ Q (F.datum k)) ∧
    (∫ x in ball (p k) (r k/16),
      |(1/2:ℝ)*localGamma μ Q u u x-(1/2:ℝ)*localGamma μ Q (F.datum k) (F.datum k) x| ∂μ)≤
        (J+B/2)*(r k)^2*(F.source k).real (ball (p k) (r k)) := by
  have hsub : ball (p k) (r k/16)⊆ball (p k) (r k) :=
    ball_subset_ball (by linarith [hr k])
  refine ⟨positive_defect_mono μ Q hsub (F.datum k) (F.source k)
    ((n:ℝ)+κ*(4*r k)^2) (F.defect k),?_,?_⟩
  · exact ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (show r k/16≤4*r k by linarith [hr k]))
      (positiveSquaredDistance_energy_value μ Q (mul_nonneg (by norm_num) (hr k).le)
        (F.cutoff k) (F.eikonal k))
  · have hΓ := localGamma_pair_congr_ae μ Q hu hu
    calc
      _ = ∫ x in ball (p k) (r k/16),
          |(1/2:ℝ)*localGamma μ Q (F.replacement k) (F.replacement k) x-
            (1/2:ℝ)*localGamma μ Q (F.datum k) (F.datum k) x| ∂μ := by
        apply integral_congr_ae
        filter_upwards [hΓ] with x hx
        rw [hx]
      _ ≤ ∫ x in ball (p k) (r k),
          |(1/2:ℝ)*localGamma μ Q (F.replacement k) (F.replacement k) x-
            (1/2:ℝ)*localGamma μ Q (F.datum k) (F.datum k) x| ∂μ :=
        setIntegral_mono_set
          ((((localGamma_memL1 μ Q (F.replacement k) (F.replacement k)).const_mul (1/2:ℝ)).sub
            ((localGamma_memL1 μ Q (F.datum k) (F.datum k)).const_mul (1/2:ℝ))).abs.integrableOn)
          (Filter.Eventually.of_forall fun _ => abs_nonneg _) (Filter.Eventually.of_forall hsub)
      _ ≤ _ := F.density_error k

end RegularPointCoordinates

end

end OAI
