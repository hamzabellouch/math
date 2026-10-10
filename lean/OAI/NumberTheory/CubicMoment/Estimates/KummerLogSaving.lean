import OAI.NumberTheory.CubicMoment.Estimates.PrimeLogSavingPowers
import OAI.NumberTheory.CubicMoment.Estimates.PublishedKummerPrime

namespace OAI

/-! Arbitrary logarithmic saving for actual independent prime weights,
uniform in logarithmic Mellin height and logarithmic conductor. -/
noncomputable section
namespace CubicFirstMoment

theorem kummer_logarithmic_prime_saving {γ : Type*}
    (hSW : KummerPrimeSiegelWalfisz) {L : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily L W) (hlo : ∀ r x, x < 1 → W r x = 0)
    {c R A : ℝ} (hc : 0 < c) (hR : 1 ≤ R) (hA : 0 < A)
    (k U : ℕ) (hk : 0 < k) :
    ∃ K Y₀ : ℝ, 0 < K ∧ 1 < Y₀ ∧ ∀ (r : γ) (Y : ℝ), Y₀ ≤ Y →
      1 ≤ Real.log (L r) → (L r)^c ≤ Y →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ (Real.log Y)^A → ∀ u : ℝ, |u| ≤ (1+Real.log (L r))^U →
      ‖smoothPrimeCharacterSum R Y (W r) (fun p => cubicSymbol p v) u‖ ≤
        K*Y/(1+Real.log (L r))^k := by
  obtain ⟨M,m,hM,hMb⟩ := hW.norm_log_bound
  obtain ⟨B,b,hB,hBb⟩ := hW.radial_deriv_bound
  let N := m+b+U
  have hD : (0:ℝ) < (N+k:ℕ) := by exact_mod_cast (show 0 < N+k by omega)
  obtain ⟨C,Y₀,hC,hY₀,hbound⟩ := scaled_kummer_prime_bound hSW hA hD
  let V := 2*M+(R-1)*(B+M)
  let K₀ := C*R*V*(2/c)^(N+k)
  let K := max 1 K₀
  have hV : 0 ≤ V := add_nonneg (mul_nonneg (by norm_num) hM)
    (mul_nonneg (sub_nonneg.mpr hR) (add_nonneg hB hM))
  refine ⟨K,Y₀,lt_of_lt_of_le zero_lt_one (le_max_left _ _),hY₀,?_⟩
  intro r Y hY hlog hLc v hv hn hcon u hu
  let z := 1+Real.log (L r)
  have hLp : 0 < L r := zero_lt_one.trans_le (hW.length_one r)
  have hz : 1 ≤ z := by dsimp [z]; linarith
  have hzp : 0 < z := zero_lt_one.trans_le hz
  obtain ⟨hlogY,hcompare⟩ := log_length_comparison hLp hc hlog hLc
  have hYp : 0 < Y := zero_lt_one.trans (hY₀.trans_le hY)
  have hb := hbound Y R (M*z^m) (B*z^b) (W r) hY hR
    (mul_nonneg hM (pow_nonneg hzp.le _)) (mul_nonneg hB (pow_nonneg hzp.le _))
    (hW.smooth r) (hlo r) (hMb r) (hBb r) v hv hn hcon u
  have hv : 2*(M*z^m)+(R-1)*(B*z^b+M*z^m*|u|) ≤ V*z^N := by
    simpa only [V,N,mul_assoc] using log_variation_power hz hR hM hB m b U hu
  have hquot : z^N/(Real.log Y)^(N+k) ≤ (2/c)^(N+k)/z^k :=
    log_power_quotient hzp hlogY hcompare N k
  have hfac : 0 ≤ C*(R*Y)/(Real.log Y)^(N+k) :=
    div_nonneg (mul_nonneg hC.le (mul_nonneg (zero_le_one.trans hR) hYp.le))
      (pow_nonneg hlogY.le _)
  calc
    _ ≤ (C*(R*Y)/(Real.log Y)^(N+k))*(V*z^N) := by
      apply hb.trans
      simpa only [Real.rpow_natCast] using mul_le_mul_of_nonneg_left hv hfac
    _ = (C*R*V*Y)*(z^N/(Real.log Y)^(N+k)) := by ring
    _ ≤ (C*R*V*Y)*((2/c)^(N+k)/z^k) :=
      mul_le_mul_of_nonneg_left hquot
        (mul_nonneg (mul_nonneg (mul_nonneg hC.le (zero_le_one.trans hR)) hV) hYp.le)
    _ = K₀*Y/z^k := by dsimp [K₀]; ring
    _ ≤ K*Y/z^k := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hYp.le) (pow_nonneg hzp.le _)

end CubicFirstMoment

end

end OAI
