import OAI.Geometry.RCD.Metric.InwardLocality
import OAI.Geometry.RCD.Sobolev.WeakRadialCancellation

namespace OAI

/-! # Independence of the squared-distance energy from its outer cutoff -/

open Set Metric MeasureTheory
open scoped NNReal

namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

theorem inwardQuadratic_constant_difference (p : X) {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R) :
    SobolevSpace.toLp μ hQ (inwardQuadratic μ hQ p (hr.trans hrR) - inwardQuadratic μ hQ p hr)
      =ᵐ[μ.restrict (ball p r)] fun _ => (r ^ 2 - R ^ 2) / 2 := by
  filter_upwards [ae_restrict_of_ae (inwardQuadratic_coe μ hQ p (hr.trans hrR)),
    ae_restrict_of_ae (inwardQuadratic_coe μ hQ p hr),
    ae_restrict_of_ae (Lp.coeFn_sub
      (SobolevSpace.toLp μ hQ (inwardQuadratic μ hQ p (hr.trans hrR)))
      (SobolevSpace.toLp μ hQ (inwardQuadratic μ hQ p hr))),
    ae_restrict_mem measurableSet_ball] with x hR hrr hs hx
  have hd : dist p x < r := by simpa only [mem_ball, dist_comm] using hx
  change (SobolevSpace.toLp μ hQ (inwardQuadratic μ hQ p (hr.trans hrR)) -
    SobolevSpace.toLp μ hQ (inwardQuadratic μ hQ p hr)) x = _
  simp only [hs, Pi.sub_apply, hR, hrr, inwardDistance,
    max_eq_left (sub_nonneg.mpr hd.le), max_eq_left (sub_nonneg.mpr (hd.le.trans hrR))]
  ring

theorem inwardQuadratic_energy_radius (p : X) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (g : SobolevSpace μ hQ) (v : X → ℝ) {L : ℝ≥0}
    (hv : LipschitzWith L v) (hc : HasCompactSupport v) (hs : tsupport v ⊆ ball p r)
    (hrep : SobolevSpace.toLp μ hQ g =ᵐ[μ] v) :
    energyForm μ hQ (inwardQuadratic μ hQ p (hr.trans hrR)) g =
      energyForm μ hQ (inwardQuadratic μ hQ p hr) g := by
  let φ : SobolevSpace.dirichlet μ hQ (ball p r) :=
    ⟨g, (SobolevSpace.dirichletCore μ hQ (ball p r)).le_topologicalClosure
      ⟨v, L, hv, hc, hs, hrep⟩⟩
  change energyForm μ hQ _ φ.val = energyForm μ hQ _ φ.val
  rw [← integral_localGamma_dirichlet μ hQ _ measurableSet_ball _ φ,
    ← integral_localGamma_dirichlet μ hQ _ measurableSet_ball _ φ]
  exact integral_congr_ae (localGamma_eq_of_constant_difference μ hQ (ball p r)
    _ _ g _ (inwardQuadratic_constant_difference μ hQ p hr hrR))

end RegularPointCoordinates

end OAI
