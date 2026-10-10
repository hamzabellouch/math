import OAI.Geometry.RCD.Heat.HeatLaplacianContraction

namespace OAI

/-! # Strong value and source limits of the actual heat regularizations -/

open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)

theorem heat_regularization_value_source_converges
    (u : SobolevSpace μ Q) (d : Lp ℝ 2 μ) (hd : IsWeakLaplacian μ Q u d)
    (t : ℕ → ℝ) (ht : ∀ k, 0 < t k) (hzero : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun k => heatSobolev μ Q (t k) (ht k) (SobolevSpace.toLp μ Q u))
      atTop (𝓝 u) ∧
    Tendsto (fun k => SobolevSpace.toLp μ Q
      (heatSobolevMap μ Q (t k/2) (half_pos (ht k))
        (-heatGeneratorAt μ Q (t k-t k/2) (SobolevSpace.toLp μ Q u))))
      atTop (𝓝 d) := by
  constructor
  · have hh := ((heatH1_continuous μ Q u).tendsto 0).comp hzero
    rw [heatH1_zero] at hh
    apply hh.congr'
    filter_upwards [] with k
    simp only [Function.comp_apply,heatH1,dite_eq_left (ht k)]
  · have hh := ((heatAt_continuous μ Q d).tendsto 0).comp hzero
    rw [heatAt_zero,one_apply_eq_self] at hh
    apply hh.congr'
    filter_upwards [] with k
    exact (heatTail_laplacian_toLp μ Q u d hd (ht k)).symm

end RegularPointCoordinates

end

end OAI
