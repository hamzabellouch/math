import Mathlib
import OAI.MathematicalPhysics.RecorderFlows.Effective

namespace OAI

/-! The initialized solenoidal-flow conclusion as a mathematical specification. -/

namespace Solenoidal
def Initialized : Prop :=
  ∃ (U : (M : Machine) → List M.Symbol → Fluid.Field) (V : Machine → Fluid.Field)
      (eval bounds : Effective.OracleCode),
    (∀ (M : Machine) (w : List M.Symbol) (p : Fluid.SpaceTime),
      1 ≤ p 0 → U M w p = V M (Fluid.translateTime (-1) p)) ∧
    Effective.RelativeEffective (fun ν M w => Fluid.force ν (U M w)) eval bounds ∧
    (∀ ν : ℝ, 0 < ν → Effective.ComputableReal ν →
      Effective.EffectiveAt (fun μ M w => Fluid.force μ (U M w)) ν) ∧
    (∀ ν : ℝ, 0 < ν → ∀ (M : Machine) (w : List M.Symbol),
      Fluid.FluidAssertions ν (U M w) (Fluid.force ν (U M w)) ∧
      Fluid.BoundedPeriodicAssertions (U M w) (Fluid.force ν (U M w)) ∧
      Fluid.ObservationAssertion M w (U M w)) ∧
    (∀ ν : ℝ, 0 < ν → ∀ (M : Machine) (w w' : List M.Symbol) (p : Fluid.SpaceTime),
      1 ≤ p 0 → Fluid.force ν (U M w) p = Fluid.force ν (U M w') p)
end Solenoidal

end OAI
