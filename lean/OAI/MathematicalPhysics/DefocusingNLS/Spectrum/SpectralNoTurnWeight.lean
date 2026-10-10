import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Order.Field

namespace OAI

/-! The no-turn norm also has a diverging uniform weight floor. Combining
it with a turning-channel floor makes the coupled Green coefficient vanish. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralNoTurn_weight_lower (b eta omega gamma C R r : ℝ)
    (hb : 0 ≤ b) (hw : 0 < omega) (hR : 0 < R) (hr : R ≤ r)
    (hL : eta+99/4 ≤ C*omega) (hCR : 2*C ≤ R^2) :
    Real.sqrt (Real.sqrt (omega/2)) ≤
      Real.sqrt ‖spectralLiouvilleMomentum 1 (-1) b eta omega gamma r‖ :=
  Real.sqrt_le_sqrt (spectralNoTurn_momentum_lower b eta omega gamma C R r hb hw hR hr hL hCR)

theorem spectralNoTurn_weight_floor_tendsto (omega : ℕ → ℝ)
    (hw : Tendsto omega atTop atTop) :
    Tendsto (fun n => Real.sqrt (Real.sqrt (omega n/2))) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp (hw.atTop_div_const (by norm_num)))

theorem spectralCommonWeight_tendsto (kp km : ℕ → ℝ)
    (hp : Tendsto kp atTop atTop) (hm : Tendsto km atTop atTop) :
    Tendsto (fun n => min (kp n) (km n)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [hp.eventually (eventually_ge_atTop B),hm.eventually (eventually_ge_atTop B)] with n hn hn'
  exact le_min hn hn'

theorem spectralCommonGreenCoefficient_tendsto (kap : ℕ → ℝ)
    (hk : Tendsto kap atTop atTop) (A C R : ℝ) :
    Tendsto (fun n => A*C/((kap n)^2*R)) atTop (𝓝 0) := by
  have hi := ((tendsto_inv_atTop_zero.comp hk).pow 2).const_mul (A*C/R)
  convert hi using 1
  · funext n
    dsimp only [Function.comp_def]
    ring
  · simp only [zero_pow (by norm_num : 2 ≠ 0),mul_zero]

end DefocusingNLS

end OAI
