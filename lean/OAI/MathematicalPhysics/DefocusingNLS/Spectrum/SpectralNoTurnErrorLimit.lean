import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnBranch
import Mathlib.Topology.Algebra.Order.Field

namespace OAI

/-! The explicit no-turn branch error vanishes with the escaping imaginary
spectral parameter. -/

open Filter Topology
namespace DefocusingNLS

noncomputable def spectralNoTurnResidualBound (C R omega : ℝ) : ℝ :=
  2*((5/16)*(2/R+4*C/R^3)+3/(4*R))/Real.sqrt (omega/2)

noncomputable def spectralNoTurnBranchError (C R omega E : ℝ) : ℝ :=
  let B := (5/2 : ℝ)*Real.exp 256
  let J := spectralNoTurnResidualBound C R omega
  6*(B^2)^2*Real.exp (B^2*J)*J+B^2*264/E^2

theorem spectralNoTurn_branch_error_tendsto (omega E : ℕ → ℝ) (C R : ℝ)
    (hw : Tendsto omega atTop atTop) (hE : Tendsto E atTop atTop) :
    Tendsto (fun n => spectralNoTurnBranchError C R (omega n) (E n)) atTop (𝓝 0) := by
  let B : ℝ := (5/2)*Real.exp 256
  have hroot : Tendsto (fun n => Real.sqrt (omega n/2)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (hw.atTop_div_const (by norm_num))
  have hj : Tendsto (fun n => spectralNoTurnResidualBound C R (omega n)) atTop (𝓝 0) := by
    have ht := (tendsto_inv_atTop_zero.comp hroot).const_mul
      (2*((5/16 : ℝ)*(2/R+4*C/R^3)+3/(4*R)))
    convert ht using 1
    · funext n
      dsimp only [spectralNoTurnResidualBound,Function.comp_def]
      ring
    · rw [mul_zero]
  have he : Tendsto (fun n => (E n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hE
  have ht := (((Real.continuous_exp.tendsto _).comp (hj.const_mul (B^2))).mul hj).const_mul (6*(B^2)^2)
  have hs := (he.pow 2).const_mul (B^2*264)
  convert ht.add hs using 1
  · funext n
    dsimp only [spectralNoTurnBranchError,B,Function.comp_def]
    ring
  · simp only [mul_zero,Real.exp_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero]

end DefocusingNLS

end OAI
