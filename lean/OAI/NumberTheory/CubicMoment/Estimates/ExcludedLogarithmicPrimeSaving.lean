import OAI.NumberTheory.CubicMoment.Estimates.PrimeExclusionSavingPowers

namespace OAI

/-! The actual low-height prime Siegel–Walfisz bound, including any
polynomially bounded excluded element. No exclusion estimate is assumed. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem excluded_logarithmic_prime_saving {γ : Type*}
    (hSW : CubicPrimeSiegelWalfisz) {L : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily L W) (hlo : ∀ r x, x < 1 → W r x = 0)
    {c d R A : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hR : 1 ≤ R) (hA : 0 < A)
    (k U : ℕ) (hk : 0 < k) :
    ∃ K Y₀ L₀ : ℝ, 0 < K ∧ 1 < Y₀ ∧ ∀ (r : γ) (Y : ℝ), Y₀ ≤ Y → L₀ ≤ L r →
      1 ≤ Real.log (L r) → (L r)^c ≤ Y →
      ∀ q₁ q₂ : Eisenstein, primary q₁ → primary q₂ → Squarefree q₁ → Squarefree q₂ →
      IsCoprime q₁ q₂ → MixedCubicNonprincipal q₁ q₂ →
      norm (q₁*q₂) ≤ (Real.log Y)^A →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ (L r)^d → ∀ u : ℝ,
      |u| ≤ (1+Real.log (L r))^U →
      ‖excludedSmoothPrimeCharacterSum R Y (W r) (mixedCubic q₁ q₂) e u‖ ≤
        K*Y/(1+Real.log (L r))^k := by
  obtain ⟨K,Y₀,hK,hY₀,hbase⟩ := logarithmic_prime_saving hSW hW hlo hc hR hA k U hk
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
  intro r Y hY hL hlog hrough q₁ q₂ h₁ h₂ hs₁ hs₂ hcop hnon hcon e he heL u hu
  have hmain := hbase r Y hY hlog hrough q₁ q₂ h₁ h₂ hs₁ hs₂ hcop hnon hcon u hu
  have hn : 0 ≤ 1+Real.log (L r) := by linarith
  have hχ : ∀ p ∈ primeCutoff (R*Y), ‖mixedCubic q₁ q₂ p‖ ≤ 1 := by
    intro p _
    rw [mixedCubic,norm_mul,norm_star]
    simpa only [one_mul] using mul_le_mul (norm_cubicSymbol_le_one h₁ p)
      (norm_cubicSymbol_le_one h₂ p) (_root_.norm_nonneg _) zero_le_one
  have herr := herror R Y (M*(1+Real.log (L r))^m) (W r) (mixedCubic q₁ q₂)
    (mul_nonneg hM (pow_nonneg hn _)) (hMb r) hχ e he u
  have habs := hL₀ (L r) hL Y (norm e) (norm_nonneg _) heL hrough
  have herr' : ‖excludedSmoothPrimeCharacterSum R Y (W r) (mixedCubic q₁ q₂) e u-
      smoothPrimeCharacterSum R Y (W r) (mixedCubic q₁ q₂) u‖ ≤ Y/(1+Real.log (L r))^k := by
    apply herr.trans
    convert habs using 1; ring
  calc
    _ = ‖smoothPrimeCharacterSum R Y (W r) (mixedCubic q₁ q₂) u+
        (excludedSmoothPrimeCharacterSum R Y (W r) (mixedCubic q₁ q₂) e u-
          smoothPrimeCharacterSum R Y (W r) (mixedCubic q₁ q₂) u)‖ := by
      congr 1
      ring
    _ ≤ ‖smoothPrimeCharacterSum R Y (W r) (mixedCubic q₁ q₂) u‖+
        ‖excludedSmoothPrimeCharacterSum R Y (W r) (mixedCubic q₁ q₂) e u-
          smoothPrimeCharacterSum R Y (W r) (mixedCubic q₁ q₂) u‖ := norm_add_le _ _
    _ ≤ K*Y/(1+Real.log (L r))^k+Y/(1+Real.log (L r))^k := add_le_add hmain herr'
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
