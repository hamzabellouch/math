import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGreenBranchBounds
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningWeightEscape
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGreenSmallness

namespace OAI

/-! In the regularized turning norm the full Green correction is bounded
by a fixed constant times the vanishing Airy scale. -/

open Set
namespace DefocusingNLS

theorem spectralTurning_green_integral_bound
    (h b eta omega gamma d R E r A C M : ℝ)
    (hd : 0 < d) (hR : 0 < R) (hr : r ∈ Icc R E)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (D U : ℝ → ℂ × ℂ) (W : ℂ) (f : ℝ → ℂ)
    (hDc : ContinuousOn D (Icc R E)) (hUc : ContinuousOn U (Icc R E))
    (hfc : ContinuousOn f (Icc R E)) (hW : W ≠ 0)
    (hdet : spectralScalarWronskian (D r) (U r) = W)
    (hgreen : ∀ t ∈ Icc R E,
      let k := spectralTurningRegularizedWeight h b eta omega gamma d
      spectralShellNorm (k r) (spectralScalarGreenState D U W r t) ≤ A/(k t))
    (hforcing : ∀ t ∈ Icc R E, ‖f t‖ ≤ C/((Real.sqrt d)⁻¹*t^2)*M) :
    spectralShellNorm (spectralTurningRegularizedWeight h b eta omega gamma d r)
      (spectralScalarGreenIntegral R E D U W f r) ≤ ((A+1)*C/R)*d*M := by
  let k := spectralTurningRegularizedWeight h b eta omega gamma d
  have hkap : 0 < (Real.sqrt d)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hd)
  obtain ⟨hl,hright⟩ := spectralGreen_closed_branch_bounds D U W k R E A (Real.sqrt d)⁻¹ r
    hr hA hkap (fun t _ => spectralTurning_weight_floor h b eta omega gamma d t) hW hdet hgreen
  have hb := spectralScalarGreenIntegral_small R E r (k r) (Real.sqrt d)⁻¹ (A+1) C M hR hr
    (spectralTurningRegularizedWeight_pos h b eta omega gamma d r hd).le hkap
    (by linarith) hC hM D U W f hDc hUc hfc hl hright hforcing
  apply hb.trans_eq
  rw [inv_pow,Real.sq_sqrt hd.le]
  field_simp

end DefocusingNLS

end OAI
