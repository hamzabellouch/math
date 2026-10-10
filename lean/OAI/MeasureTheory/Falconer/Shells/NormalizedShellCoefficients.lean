import OAI.MeasureTheory.Falconer.Geometry.NormalizedInverseFactors

namespace OAI

/-! # Uniform radial coefficients after the stationary shell normalization

The inverse order pays for the sum of the two endpoint derivative orders.
The remaining radial ratio is bounded on the fixed shell, independently of
its frequency and cell depth.
-/

namespace Falconer

theorem normalized_stationary_coefficient_le {p q j : ℕ}
    (hpq : p+q ≤ 2*j) {Λ D s h : ℝ} (hΛ : 0 < Λ) (hD : 1 ≤ D)
    (hs : 0 < s) (hh : 0 ≤ h) (hDΛ : D^2 ≤ Λ) (hΛs : Λ ≤ 4*s) :
    |Λ^h*(Λ^j)⁻¹*D^(p+q)/(s^h)| ≤ 4^h := by
  have hc : 0 ≤ Λ^h*(Λ^j)⁻¹*D^(p+q) := by positivity
  rw [abs_of_nonneg (div_nonneg hc (Real.rpow_nonneg hs.le _))]
  have hratio : D^2/Λ ≤ 1 := (div_le_one hΛ).mpr hDΛ
  have hpow : (D^2/Λ)^j ≤ 1 := pow_le_one₀ (by positivity) hratio
  have hnum : Λ^h*(Λ^j)⁻¹*D^(p+q) ≤ Λ^h :=
    (stationary_normalized_coefficient_le hpq hΛ hD h).trans
      ((mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hΛ.le _)).trans_eq (mul_one _))
  calc
    _ ≤ Λ^h/s^h := div_le_div_of_nonneg_right hnum (Real.rpow_nonneg hs.le _)
    _ = (Λ/s)^h := (Real.div_rpow hΛ.le hs.le h).symm
    _ ≤ 4^h := Real.rpow_le_rpow (by positivity) ((div_le_iff₀ hs).mpr hΛs) hh

theorem restored_normalized_stationary_coefficient_le {p q j : ℕ}
    (hpq : p+q ≤ 2*j) {A E Λ D s h : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hΛ : 0 < Λ) (hD : 1 ≤ D) (hs : 0 < s) (hh : 0 ≤ h)
    (hDΛ : D^2 ≤ Λ) (hΛs : Λ ≤ 4*s) :
    |Λ^h*(Λ^j)⁻¹*((A*D^p)*(E*D^q))/(s^h)| ≤ A*E*4^h := by
  have hid : Λ^h*(Λ^j)⁻¹*((A*D^p)*(E*D^q))/(s^h) =
      (A*E)*(Λ^h*(Λ^j)⁻¹*D^(p+q)/(s^h)) := by
    rw [pow_add]
    ring
  rw [hid,abs_mul,abs_of_nonneg (mul_nonneg hA hE)]
  exact mul_le_mul_of_nonneg_left
    (normalized_stationary_coefficient_le hpq hΛ hD hs hh hDΛ hΛs) (mul_nonneg hA hE)

end Falconer

end OAI
