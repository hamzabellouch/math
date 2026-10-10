import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TorusClassSmoothSlice

namespace OAI

noncomputable section
namespace VelocityDetection.BurstTotal
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open ChartRouting BurstSchedule Periodization
variable (A : RoutingData) (ν : ℝ)

theorem comparisonClass (hν : 0 < ν) (q : ℕ) :
    TorusClass.ComparisonClass (velocity A ν hν q) (fun _ _ => 0) :=
  TorusClass.ComparisonClass.of_smooth (contDiff_velocity A ν hν q) contDiff_const
    (fun t _ => velocity_periodic A ν hν q t) (fun _ _ _ _ _ => rfl) (by simp)

theorem unique (hν : 0 < ν) (q : ℕ) {v : VectorField 3} {p : ScalarField 3}
    (hv : TorusClass.ComparisonClass v p) (hNS : NavierStokes ν v p (force A ν q)) :
    ∀ t ≥ 0, (∀ x, v t x = velocity A ν hν q t x) ∧ (∀ x, p t x = 0) :=
  TorusClass.comparison_unique hν.le (comparisonClass A ν hν q) hv (navierStokes A ν hν q) hNS

end VelocityDetection.BurstTotal
end

end OAI
