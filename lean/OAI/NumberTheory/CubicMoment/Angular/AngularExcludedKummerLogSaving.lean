import OAI.NumberTheory.CubicMoment.Estimates.PrimeExclusionSavingPowers
import OAI.NumberTheory.CubicMoment.Angular.AngularKummerLogSaving

namespace OAI

/-! The actual low-height prime Siegel–Walfisz bound, including any
polynomially bounded excluded element. No exclusion estimate is assumed. -/
noncomputable section
open Filter
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_excluded_kummer_logarithmic_prime_saving {γ : Type*}
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) {L : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily L W) (hlo : ∀ r x, x < 1 → W r x = 0)
    {c d R A : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hR : 1 ≤ R) (hA : 0 < A)
    (k U : ℕ) (hk : 0 < k) :
    ∃ K Y₀ L₀ : ℝ, 0 < K ∧ 1 < Y₀ ∧ ∀ (r : γ) (Y : ℝ), Y₀ ≤ Y → L₀ ≤ L r →
      1 ≤ Real.log (L r) → (L r)^c ≤ Y →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ (Real.log Y)^A →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ (L r)^d → ∀ u : ℝ,
      |u| ≤ (1+Real.log (L r))^U →
      ‖excludedSmoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) e u‖ ≤
        K*Y/(1+Real.log (L r))^k := by
  obtain ⟨K,Y₀,hK,hY₀,hbase⟩ := angular_kummer_logarithmic_prime_saving ℓ hSW hℓ hW hlo hc hR hA k U hk
  let ε := c/(2*(d+1))
  have hε : 0 < ε := div_pos hc (by positivity)
  have hgap : d*ε < c := by
    have he : ε*(2*(d+1)) = c := div_mul_cancel₀ c (by positivity : 2*(d+1) ≠ 0)
    nlinarith [mul_nonneg hε.le hd]
  obtain ⟨C,hC,herror⟩ := excluded_prime_input_error hε
  obtain ⟨M,m,hM,hMb⟩ := hW.norm_log_bound
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp
    (exclusion_log_absorption hε hgap (mul_nonneg hC.le hM) m k)
  refine ⟨K+1,Y₀,L₀,by linarith,hY₀,?_⟩
  intro r Y hY hL hlog hrough v hv hn hcon e he heL u hu
  have hmain := hbase r Y hY hlog hrough v hv hn hcon u hu
  have hn : 0 ≤ 1+Real.log (L r) := by linarith
  have hχ : ∀ p ∈ primeCutoff (R*Y), ‖angularKummerCharacter ℓ v p‖ ≤ 1 := by
    intro p hp
    unfold angularKummerCharacter
    rw [norm_mul,norm_theta (primary_ne_zero (mem_primeCutoff.mp hp).1.1) ℓ,one_mul]
    exact norm_cubicSymbol_le_one (mem_primeCutoff.mp hp).1.1 v
  have herr := herror R Y (M*(1+Real.log (L r))^m) (W r) (angularKummerCharacter ℓ v)
    (mul_nonneg hM (pow_nonneg hn _)) (hMb r) hχ e he u
  have habs := hL₀ (L r) hL Y (norm e) (norm_nonneg _) heL hrough
  have herr' : ‖excludedSmoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) e u-
      smoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) u‖ ≤ Y/(1+Real.log (L r))^k := by
    apply herr.trans
    convert habs using 1; ring
  calc
    _ = ‖smoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) u+
        (excludedSmoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) e u-
          smoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) u)‖ := by
      congr 1
      ring
    _ ≤ ‖smoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) u‖+
        ‖excludedSmoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) e u-
          smoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) u‖ := norm_add_le _ _
    _ ≤ K*Y/(1+Real.log (L r))^k+Y/(1+Real.log (L r))^k := add_le_add hmain herr'
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
