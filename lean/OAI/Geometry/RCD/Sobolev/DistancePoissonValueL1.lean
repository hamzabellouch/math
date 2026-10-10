import OAI.Geometry.RCD.Sobolev.DistancePoissonFamily
import OAI.Geometry.RCD.Coordinates.NormalizedL1FromL2

namespace OAI

/-! # The actual normalized Poisson value error also vanishes in L1 -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {Q : QuadraticCheegerEnergy μ}
  {n : ℕ} {κ B J C : ℝ} {p : ℕ → X} {r : ℕ → ℝ} {hr : ∀ k, 0<r k}
  (F : DistancePoissonFamily μ Q n κ B J C p r hr)

theorem DistancePoissonFamily.normalized_value_L1_tendsto_zero {P : ℝ} (hP : 0≤P)
    (hV : ∀ k, 0<μ.real (ball (p k) (r k)))
    (hpoin : ∀ k, ∀ v : SobolevSpace.dirichlet μ Q (ball (p k) (r k)),
      ‖SobolevSpace.toLp μ Q v.val‖^2≤P*(r k)^2*energyForm μ Q v.val v.val)
    (hmass : Tendsto (fun k => (F.source k).real (ball (p k) (r k))/μ.real (ball (p k) (r k)))
      atTop (𝓝 0)) :
    Tendsto (fun k => (μ.real (ball (p k) (r k)))⁻¹*
      ∫ x in ball (p k) (r k),
        |SobolevSpace.toLp μ Q (((r k)^2)⁻¹ • (F.datum k-F.replacement k)) x| ∂μ) atTop (𝓝 0) := by
  have hlim := (F.normalized_value_error_tendsto_zero hP hV hpoin hmass).pow 2
  simp_rw [normalized_sobolev_mean_sq] at hlim
  simp only [zero_pow (by norm_num : 2≠0)] at hlim
  apply normalized_l1_tendsto_of_l2 μ (fun k => ball (p k) (r k))
    (fun k => (μ.real (ball (p k) (r k)))⁻¹) (fun _ => by positivity)
    (fun k => by rw [inv_mul_cancel₀ (hV k).ne'])
    (fun k => SobolevSpace.toLp μ Q (((r k)^2)⁻¹ • (F.datum k-F.replacement k)))
    _ (Eventually.of_forall fun k => (Lp.memLp _).integrable_sq.integrableOn)
    (fun _ => measure_ball_lt_top.ne) hlim
  intro k
  let : IsFiniteMeasure (μ.restrict (ball (p k) (r k))) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  exact ((Lp.memLp _).restrict (ball (p k) (r k))).integrable (by norm_num)

end RegularPointCoordinates

end

end OAI
