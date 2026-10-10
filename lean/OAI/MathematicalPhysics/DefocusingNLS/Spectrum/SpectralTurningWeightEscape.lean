import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRegularizedWeight
import Mathlib.Topology.Algebra.Order.Field

namespace OAI

/-! The regularized weight has a spatially uniform lower bound tending to
infinity, even at the moving turning point. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_weight_floor_tendsto (d : ℕ → ℝ)
    (hd : Tendsto d atTop (𝓝 0)) (hdpos : ∀ᶠ n in atTop, 0 < d n) :
    Tendsto (fun n => (Real.sqrt (d n))⁻¹) atTop atTop := by
  have hs : Tendsto (fun n => Real.sqrt (d n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hd
  apply tendsto_inv_nhdsGT_zero.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨hs,hdpos.mono (fun n hn => Real.sqrt_pos.mpr hn)⟩

theorem spectralTurning_weight_floor (h b eta omega gamma d r : ℝ) :
    (Real.sqrt d)⁻¹ ≤ spectralTurningRegularizedWeight h b eta omega gamma d r :=
  le_max_left _ _

theorem spectralTurning_green_coefficient_tendsto (d : ℕ → ℝ)
    (hd : Tendsto d atTop (𝓝 0)) (hdpos : ∀ᶠ n in atTop, 0 < d n)
    (A C R : ℝ) (_hR : 0 < R) :
    Tendsto (fun n => A*C/(((Real.sqrt (d n))⁻¹)^2*R)) atTop (𝓝 0) := by
  have he : ∀ᶠ n in atTop,
      A*C/(((Real.sqrt (d n))⁻¹)^2*R) = (A*C/R)*d n := by
    filter_upwards [hdpos] with n hn
    rw [inv_pow,Real.sq_sqrt hn.le]
    field_simp
  apply Tendsto.congr' (he.mono (fun _ hn => hn.symm))
  simpa only [mul_zero] using hd.const_mul (A*C/R)

end DefocusingNLS

end OAI
