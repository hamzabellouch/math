import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedHoppingBound
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PolynomialConstantBounds

namespace OAI

/-! Explicit natural exponents make calibrated hopping perturbatively
small and leave an inverse-polynomial fraction of its squared scale. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem pow_mul_inverse_add {N : ℝ} (hN : 0 < N) (a b : ℕ) :
    N ^ a * (N ^ (a + b))⁻¹ = (N ^ b)⁻¹ := by
  rw [pow_add, mul_inv_rev]
  field_simp [pow_ne_zero a hN.ne', pow_ne_zero b hN.ne']

theorem inverse_power_lt_half {N : ℝ} (hN : 2 ≤ N) {E : ℕ} (hE : 2 ≤ E) :
    (N ^ E)⁻¹ < 1 / 2 := by
  have hNp : 0 < N := by linarith
  have hp : (4 : ℝ) ≤ N ^ E := by
    have hs : (4 : ℝ) ≤ N ^ 2 := by nlinarith
    exact hs.trans (pow_le_pow_right₀ (by linarith : 1 ≤ N) hE)
  have hi : (N ^ E)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
  exact hi.trans_lt (by norm_num)

theorem polynomial_hopping_smallness {Edge : Type*} [Fintype Edge]
    {freq scale N : ℝ} (hN : 2 ≤ N) (R A L E : ℕ)
    (hc : (N ^ L)⁻¹ ≤ localizedGramConstant freq)
    (hU : Real.sqrt (localizedCoulombProfile freq 0) ≤ N ^ L)
    (hr : (Fintype.card Edge : ℝ) ≤ N ^ R) (distance K : Edge → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hKhi : ∀ e, K e ≤ N ^ A)
    (hcal : ∀ e, scale * planarHopping (distance e) =
      coulombHoppingTarget freq (N ^ (E + (R + A + 2 * L + 2)))⁻¹ (K e) (distance e)) :
    4 * ∑ e, |scale * planarHopping (distance e)| ≤ (N ^ E)⁻¹ * localizedGramConstant freq := by
  have hNp : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  let B := E + (R + A + 2 * L + 2)
  have hτ : 0 ≤ (N ^ B)⁻¹ := inv_nonneg.mpr (pow_nonneg hNp.le B)
  have hsqrt : Real.sqrt (N ^ A * localizedCoulombProfile freq 0) ≤ N ^ (A + L) := by
    rw [Real.sqrt_mul (pow_nonneg hNp.le A), pow_add]
    apply mul_le_mul ?_ hU (Real.sqrt_nonneg _) (pow_nonneg hNp.le A)
    apply Real.sqrt_le_iff.mpr
    have hp : 1 ≤ N ^ A := one_le_pow₀ hN₁
    exact ⟨by positivity, by nlinarith only [hp]⟩
  have hb := calibrated_hopping_sum_bound freq scale (N ^ B)⁻¹ (N ^ A) hτ distance K hK hKhi hcal
  have hbound : 4 * (Fintype.card Edge : ℝ) * ((N ^ B)⁻¹ *
      Real.sqrt (N ^ A * localizedCoulombProfile freq 0)) ≤ 4 * (N ^ (E + L + 2))⁻¹ := by
    calc
      _ ≤ 4 * N ^ R * ((N ^ B)⁻¹ * N ^ (A + L)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hr (by norm_num))
          (mul_le_mul_of_nonneg_left hsqrt hτ)
          (mul_nonneg hτ (Real.sqrt_nonneg _)) (by positivity)
      _ = 4 * (N ^ (R + (A + L)) * (N ^ B)⁻¹) := by rw [pow_add]; ring
      _ = _ := by
        rw [show B = (R + (A + L)) + (E + L + 2) by dsimp [B]; omega,
          pow_mul_inverse_add hNp]
  have hfour : 4 * (N ^ (E + L + 2))⁻¹ ≤ (N ^ (E + L))⁻¹ := by
    have hsq : (4 : ℝ) ≤ N ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hsq (pow_nonneg hNp.le (E + L))
    have hratio : 4 / N ^ (E + L + 2) ≤ 1 / N ^ (E + L) :=
      (div_le_div_iff₀ (pow_pos hNp (E + L + 2)) (pow_pos hNp (E + L))).mpr
        (by simpa only [pow_add, one_mul, mul_one, mul_comm] using h)
    simpa only [div_eq_mul_inv, one_mul] using hratio
  have hlast : (N ^ (E + L))⁻¹ ≤ (N ^ E)⁻¹ * localizedGramConstant freq := by
    have h := mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr (pow_nonneg hNp.le E))
    simpa only [pow_add, mul_inv_rev, mul_comm] using h
  exact hb.trans (hbound.trans (hfour.trans hlast))

theorem polynomial_hubbard_error_budget {N c : ℝ} (hN : 0 < N) (R A L g : ℕ)
    (hc : 2 * c ≤ N ^ L) :
    let C := R + A + 2 * L + 2
    let E := g + 2 * C + L
    let B := E + C
    2 * c * ((N ^ E)⁻¹) ^ 3 ≤ (N ^ g)⁻¹ * ((N ^ B)⁻¹) ^ 2 := by
  intro C E B
  calc
    _ ≤ N ^ L * ((N ^ E)⁻¹) ^ 3 :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg (inv_nonneg.mpr (pow_nonneg hN.le E)) 3)
    _ = N ^ L * (N ^ (E * 3))⁻¹ := by rw [inv_pow (N ^ E) 3, ← pow_mul]
    _ = (N ^ (g + B * 2))⁻¹ := by
      rw [show E * 3 = L + (g + B * 2) by dsimp [B, E, C]; omega, pow_mul_inverse_add hN]
    _ = _ := by rw [pow_add, pow_mul, mul_inv_rev, inv_pow]; ring

end ContinuumCoulomb

end

end OAI
