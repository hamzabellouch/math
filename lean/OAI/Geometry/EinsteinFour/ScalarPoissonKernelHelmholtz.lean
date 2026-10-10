import Mathlib.Analysis.Distribution.Sobolev

namespace OAI

/-! The normalized constant-coefficient Helmholtz operator gains two Sobolev
orders.  This is an identity of actual tempered-distribution operators,
deduced from the Fourier multiplier definition of the Bessel potential. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Laplacian ENNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem scalar_fourierMultiplier_add {g h : E → ℂ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) (u : 𝓢'(E, ℂ)) :
    fourierMultiplierCLM ℂ (g + h) u =
      fourierMultiplierCLM ℂ g u + fourierMultiplierCLM ℂ h u := by
  simp only [fourierMultiplierCLM_apply, smulLeftCLM_add hg hh,
    add_apply, fourierInv_add]

private theorem scalar_bessel_two_add (u : 𝓢'(E, ℂ)) :
    besselPotential E ℂ 2 u =
      u + fourierMultiplierCLM ℂ (fun x : E => Complex.ofReal (‖x‖ ^ 2)) u := by
  rw [besselPotential]
  norm_num only [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  have hsymbol : (fun x : E => Complex.ofReal (1 + ‖x‖ ^ 2)) =
      (fun _ : E => (1 : ℂ)) + (fun x : E => Complex.ofReal (‖x‖ ^ 2)) := by
    ext x
    simp only [Pi.add_apply, Complex.ofReal_add, Complex.ofReal_one]
  rw [hsymbol, scalar_fourierMultiplier_add (by fun_prop) (by fun_prop),
    fourierMultiplierCLM_const]
  simp only [ContinuousLinearMap.id_apply, one_smul]

/-- The normalization follows the Fourier convention used by Mathlib:
`J² = 1 - (2π)⁻² Δ`. -/
def normalizedScalarHelmholtz (u : 𝓢'(E, ℂ)) : 𝓢'(E, ℂ) :=
  u - ((2 * Real.pi) ^ 2)⁻¹ • Δ u

theorem normalizedScalarHelmholtz_eq_bessel (u : 𝓢'(E, ℂ)) :
    normalizedScalarHelmholtz u = besselPotential E ℂ 2 u := by
  have hπ : (2 * Real.pi) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hcoef : ((2 * Real.pi) ^ 2)⁻¹ * (-(2 * Real.pi) ^ 2) = -(1 : ℝ) := by
    rw [mul_neg, inv_mul_cancel₀ hπ]
  rw [normalizedScalarHelmholtz, laplacian_eq_fourierMultiplierCLM,
    smul_smul, hcoef, neg_one_smul, sub_neg_eq_add]
  exact (scalar_bessel_two_add u).symm

/-- No regularity is assumed for `u`: regularity of its normalized Helmholtz
image is equivalent to two additional Sobolev orders of `u`. -/
theorem normalizedScalarHelmholtz_memSobolev_iff {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : 𝓢'(E, ℂ)) :
    MemSobolev s p (normalizedScalarHelmholtz u) ↔ MemSobolev (s + 2) p u := by
  rw [normalizedScalarHelmholtz_eq_bessel, memSobolev_besselPotential_iff, add_comm (2 : ℝ)]

theorem normalizedScalarHelmholtz_gain_two {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {u f : 𝓢'(E, ℂ)} (heq : normalizedScalarHelmholtz u = f)
    (hf : MemSobolev s p f) : MemSobolev (s + 2) p u :=
  (normalizedScalarHelmholtz_memSobolev_iff u).mp (heq.symm ▸ hf)

/-- Distributional control of both `u` and its actual Laplacian gains two
orders, with no elliptic regularity premise. -/
theorem scalar_laplacian_gain_two {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {u : 𝓢'(E, ℂ)} (hu : MemSobolev s p u) (hΔ : MemSobolev s p (Δ u)) :
    MemSobolev (s + 2) p u := by
  apply (normalizedScalarHelmholtz_memSobolev_iff u).mp
  unfold normalizedScalarHelmholtz
  simpa only [Complex.coe_smul] using
    hu.sub (hΔ.smul (Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹)))

end
end PositiveEinsteinFour.Geometry

end OAI
