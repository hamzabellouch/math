import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorParameterLimit
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.OddPowerMixedIncrement
import Mathlib.Topology.Sequences

namespace OAI

/-! The actual fixed-power outgoing correction varies continuously with its parameters. -/

open Set Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem continuous_radialExterior_corrections (S : Set (ℂ × ℂ))
    (n : ℕ) (m : ℂ) (δ κ : ℝ) (hδ : 0 < δ)
    (ν : S → ℂ) (hν : Continuous ν)
    (f : S → ℝ →ᵇ ℂ) (hf : Continuous f)
    (r : S → ℝ →ᵇ ℂ × ℂ) (hr : Continuous r)
    (hκ : ∀ z, radialExteriorMatrixBound (ν z)+radialExteriorCutoffRate n m δ < κ)
    (hbase : ∀ z t, ‖f z t-m‖ ≤ δ/4)
    (v : S → ℝ →ᵇ ℂ × ℂ)
    (hv : ∀ z t, v z t=radialExteriorTailIntegral κ
      (fun s => radialExteriorErrorField κ (ν z) (radialExteriorCutoffPower n m δ)
        (f z) (r z) s (v z s)) t) :
    Continuous v := by
  obtain ⟨C,hC,hbound⟩ := exists_oddPower_mixed_increment_bound n (‖m‖+δ)
    (by positivity)
  apply SeqContinuous.continuous
  intro z z₀ hz
  exact radialExterior_tail_parameter_limit n m δ κ C hδ hC hbound
    (fun i => ν (z i)) (ν z₀) (hν.continuousAt.tendsto.comp hz) (hκ z₀)
    (fun i => f (z i)) (f z₀) (hf.continuousAt.tendsto.comp hz) (hbase z₀)
    (fun i => r (z i)) (r z₀) (hr.continuousAt.tendsto.comp hz)
    (fun i => v (z i)) (v z₀)
    (Eventually.of_forall (fun i => hv (z i))) (hv z₀)

end DefocusingNLS

end OAI
