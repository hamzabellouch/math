import OAI.Geometry.RCD.Sobolev.DistancePoissonExtensions

namespace OAI

/-! # Vanishing dimensionless gradient and density errors of the actual replacements -/

open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

private theorem radius_error_tendsto_zero (r V M E : ℕ → ℝ) {C : ℝ}
    (hr : ∀ k, 0<r k) (hV : ∀ k, 0<V k) (hE : ∀ k, 0≤E k)
    (hb : ∀ k, E k≤C*(r k)^2*M k)
    (hM : Tendsto (fun k => M k/V k) atTop (𝓝 0)) :
    Tendsto (fun k => E k/((r k)^2*V k)) atTop (𝓝 0) := by
  have hbound k : E k/((r k)^2*V k)≤C*(M k/V k) := by
    calc
      _ ≤ (C*(r k)^2*M k)/((r k)^2*V k) :=
        div_le_div_of_nonneg_right (hb k) (mul_nonneg (sq_nonneg _) (hV k).le)
      _ = _ := by field_simp [(hr k).ne']
  apply squeeze_zero (fun k => div_nonneg (hE k) (mul_nonneg (sq_nonneg _) (hV k).le)) hbound
  simpa only [mul_zero] using hM.const_mul C

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {Q : QuadraticCheegerEnergy μ}
  {n : ℕ} {κ B J C : ℝ} {p : ℕ → X} {r : ℕ → ℝ} {hr : ∀ k, 0<r k}
  (F : DistancePoissonFamily μ Q n κ B J C p r hr)

theorem DistancePoissonFamily.normalized_energy_error_tendsto_zero
    (hV : ∀ k, 0<μ.real (ball (p k) (r k)))
    (hM : Tendsto (fun k => (F.source k).real (ball (p k) (r k))/μ.real (ball (p k) (r k)))
      atTop (𝓝 0)) :
    Tendsto (fun k => (∫ x, (SobolevSpace.minimalSlope μ Q (F.datum k-F.replacement k) x)^2 ∂μ)/
      ((r k)^2*μ.real (ball (p k) (r k)))) atTop (𝓝 0) := by
  apply radius_error_tendsto_zero r (fun k => μ.real (ball (p k) (r k)))
    (fun k => (F.source k).real (ball (p k) (r k))) _ hr hV
    (fun k => integral_nonneg fun _ => sq_nonneg _)
  · intro k
    exact (F.energy_error k).trans_eq (by ring)
  · exact hM

theorem DistancePoissonFamily.normalized_density_error_tendsto_zero
    (hV : ∀ k, 0<μ.real (ball (p k) (r k)))
    (hM : Tendsto (fun k => (F.source k).real (ball (p k) (r k))/μ.real (ball (p k) (r k)))
      atTop (𝓝 0)) :
    Tendsto (fun k => (∫ x in ball (p k) (r k),
      |(1/2:ℝ)*localGamma μ Q (F.replacement k) (F.replacement k) x-
        (1/2:ℝ)*localGamma μ Q (F.datum k) (F.datum k) x| ∂μ)/
      ((r k)^2*μ.real (ball (p k) (r k)))) atTop (𝓝 0) := by
  apply radius_error_tendsto_zero r (fun k => μ.real (ball (p k) (r k)))
    (fun k => (F.source k).real (ball (p k) (r k))) _ hr hV
    (fun k => integral_nonneg fun _ => abs_nonneg _) (F.density_error) hM

end RegularPointCoordinates

end

end OAI
