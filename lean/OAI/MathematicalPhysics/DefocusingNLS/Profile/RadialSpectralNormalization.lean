import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralModeScaling
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralEnergyPositive

namespace OAI

/-! A nonzero outgoing radial mode can be normalized on any fixed ball.
No outgoing, regularity, or eigenvalue condition changes under this scaling. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem RadialSpectralMode.normalized {a b : ℝ} {m N : ℕ} {Q : ℝ → ℂ} {eta : ℝ} {lam : ℂ}
    (u : RadialSpectralMode a b m N Q (eta : ℂ) lam) (heta : 0 ≤ eta)
    (hQ : ContinuousOn Q (Ioi 0)) (R : ℝ) (hR : 0 < R) :
    ∃ v : RadialSpectralMode a b m N Q (eta : ℂ) lam,
      (∫ r in (0 : ℝ)..R, spectralRadialEnergyDensity eta v.first v.second r)=1 := by
  let E := ∫ r in (0 : ℝ)..R, spectralRadialEnergyDensity eta u.first u.second r
  have hE : 0 < E := harmonicRadialEigenpair_energy_pos a b m Q u.first u.second eta lam
    heta hQ u.first_c2 u.second_c2 u.equation u.nonzero R hR
  let c : ℂ := ((Real.sqrt E)⁻¹ : ℝ)
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr hE).ne')
  refine ⟨u.scale c hc,?_⟩
  change (∫ r in (0 : ℝ)..R, spectralRadialEnergyDensity eta
    (fun r => c*u.first r) (fun r => c*u.second r) r)=1
  rw [spectralRadialEnergyIntegral_scale]
  change ‖c‖^2*E=1
  dsimp only [c]
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg E)),
    inv_pow,Real.sq_sqrt hE.le,inv_mul_cancel₀ hE.ne']

end DefocusingNLS

end OAI
