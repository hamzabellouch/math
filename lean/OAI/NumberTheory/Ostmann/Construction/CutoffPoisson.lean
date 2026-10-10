import OAI.NumberTheory.Ostmann.Construction.ScaledPeriodicPoisson
import OAI.NumberTheory.Ostmann.SchwartzCutoff

namespace OAI

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
open FourierTransform
namespace Ostmann.Construction

theorem cutoff_periodic_poisson (Q : ℕ) [NeZero Q] (F : Fin Q → ℂ) {X : ℝ}
    (hX : 0 < X) (hperiod : (Q : ℝ)/4 < X) :
    (∑' n : ℤ, periodicResidueTest Q F n * SchwartzCutoff.psi ((n : ℝ)/X)) =
      (X/(Q : ℝ) : ℂ) * 𝓕 SchwartzCutoff.psi 0 * (∑ r, F r) := by
  apply scaled_periodic_poisson Q SchwartzCutoff.psi F hX
    (C := (1:ℝ)/4)
  · simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hperiod
  · intro ξ hξ
    exact SchwartzCutoff.fourier_psi_zero_of_abs_ge hξ.le

theorem cutoff_periodic_mean_zero (Q : ℕ) [NeZero Q] (F : Fin Q → ℂ) {X : ℝ}
    (hX : 0 < X) (hperiod : (Q : ℝ)/4 < X) (hmean : ∑ r, F r = 0) :
    (∑' n : ℤ, periodicResidueTest Q F n * SchwartzCutoff.psi ((n : ℝ)/X)) = 0 := by
  rw [cutoff_periodic_poisson Q F hX hperiod, hmean, mul_zero]

end Ostmann.Construction

end

end OAI
