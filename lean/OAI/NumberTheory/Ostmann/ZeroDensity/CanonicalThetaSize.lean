import OAI.NumberTheory.Ostmann.ZeroDensity.CanonicalRieszKernelBound
import OAI.NumberTheory.Ostmann.ZeroDensity.TotientSqrtBound
import OAI.NumberTheory.Ostmann.ZeroDensity.ThetaMainTerm

namespace OAI

/-! # Elementary size of the canonical progression main term -/

namespace Ostmann

open Complex

theorem canonical_page_beta_inverse_bound : ∃ B : ℝ, 0 < B ∧
    ∀ q : ℕ, (pageBeta (actualLocalZero q))⁻¹ ≤ B := by
  obtain ⟨C, hC, hbound⟩ := canonical_riesz_kernel_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro q
  let β := pageBeta (actualLocalZero q)
  have hβ : 0 < β := pageBeta_pos _
  have hβ1 : β ≤ 1 := pageBeta_le_one _
  have he : pageRieszKernelNorm q = 1 / (β * (β + 1)) := by
    change ‖(1 : ℂ) / ((β : ℂ) * ((β : ℂ) + 1))‖ = _
    rw [show (β : ℂ) + 1 = ((β + 1 : ℝ) : ℂ) by push_cast; rfl,
      norm_div, norm_one, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hβ, abs_of_pos (by linarith : 0 < β + 1)]
  have hb := hbound q
  rw [he] at hb
  have hid : β⁻¹ = (β + 1) * (1 / (β * (β + 1))) := by field_simp
  change β⁻¹ ≤ _
  rw [hid]
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ β + 1 by linarith)
  nlinarith

theorem thetaMainTerm_size (φ χ β X B : ℝ) (hφ : 0 < φ) (hχ : |χ| ≤ 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hX : 1 ≤ X) (_hB : 0 ≤ B) (hinv : β⁻¹ ≤ B) :
    |thetaMainTerm φ χ β X| ≤ (1 + B) * X / φ := by
  have hXp : 0 ≤ X := by linarith
  have hp : 0 ≤ X ^ β := Real.rpow_nonneg hXp _
  have hpow : X ^ β ≤ X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX hβ1
  have hc : |χ * X ^ β / β| ≤ X * B := by
    rw [abs_div, abs_mul, abs_of_nonneg hp, abs_of_pos hβ, div_eq_mul_inv]
    have h1 : |χ| * X ^ β ≤ X := (mul_le_mul_of_nonneg_right hχ hp).trans (by simpa using hpow)
    exact mul_le_mul h1 hinv (inv_nonneg.mpr hβ.le) hXp
  rw [thetaMainTerm, abs_div, abs_of_pos hφ]
  apply div_le_div_of_nonneg_right _ hφ.le
  have hh := abs_sub X (χ * X ^ β / β)
  rw [abs_of_nonneg hXp] at hh
  nlinarith

theorem canonical_theta_sqrt_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (q a : ℕ) (X : ℝ), 0 < q → 1 ≤ X →
      |thetaMainTerm q.totient (pageCoefficient (actualLocalZero q) a)
        (pageBeta (actualLocalZero q)) X| ≤ C * X / Real.sqrt q := by
  obtain ⟨B, hB, hβ⟩ := canonical_page_beta_inverse_bound
  obtain ⟨D, hD, hφ⟩ := reciprocal_totient_sqrt_bound
  refine ⟨(1 + B) * D, by positivity, ?_⟩
  intro q a X hq hX
  have hφp : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have ht := thetaMainTerm_size (q.totient : ℝ) (pageCoefficient (actualLocalZero q) a)
    (pageBeta (actualLocalZero q)) X B hφp (pageCoefficient_abs_le_one _ _)
    (pageBeta_pos _) (pageBeta_le_one _) hX hB.le (hβ q)
  have hh := mul_le_mul_of_nonneg_left (hφ q hq) (show 0 ≤ (1 + B) * X by positivity)
  calc
    _ ≤ (1 + B) * X / q.totient := ht
    _ ≤ (1 + B) * X * (D / Real.sqrt q) := by simpa only [div_eq_mul_inv, mul_one, one_mul] using hh
    _ = _ := by ring

end Ostmann

end OAI
