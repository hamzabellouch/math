import OAI.NumberTheory.CubicMoment.Estimates.RoughKummerLowHeight
import OAI.NumberTheory.CubicMoment.Estimates.StructuredResidualFrequencies

namespace OAI

/-! At low height the cube part of an arbitrary noncube frequency is
removed exactly and charged to the proved excluded-prime estimate. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem rough_noncube_low_height
    (hSW : KummerPrimeSiegelWalfisz) {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    {c d₁ d₂ R A : ℝ} (hc : 0 < c) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (hR : 1 ≤ R) (hA : 0 < A) (k U : ℕ) (hk : 0 < k) :
    ∃ K L₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (L r)^c ≤ X i) →
      ∀ v j : Eisenstein, v ≠ 0 → j ≠ 0 →
      (¬∃ a : Eisenstein, a^3 = v*j^3) → norm v ≤ (Real.log (L r))^A → norm j ≤ (L r)^d₂ →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ (L r)^d₁ → ∀ u : ℝ,
      |u| ≤ (1+Real.log (L r))^U →
      ‖fullStructuredPrimeSum R (v*j^3) 1 1 e u (W r) X‖ ≤
        K*L r/(1+Real.log (L r))^k := by
  obtain ⟨K,L₀,hK,hbound⟩ := rough_kummer_low_height hSW hW hlo hc
    (add_nonneg hd₁ hd₂) hR hA k U hk
  refine ⟨K,L₀,hK,?_⟩
  intro r X hL hprod hrough v j hv hj hn hcon hjN e he heN u hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hW.length_one (r,Classical.arbitrary ι))
  have hnv : ¬∃ a : Eisenstein, a^3 = v := by
    rintro ⟨a,ha⟩
    apply hn
    exact ⟨a*j,by rw [mul_pow,ha]⟩
  have hen : norm (e*j) ≤ (L r)^(d₁+d₂) := by
    rw [norm_mul_eq,Real.rpow_add hLp]
    exact mul_le_mul heN hjN (norm_nonneg _) (Real.rpow_nonneg hLp.le _)
  have hb := hbound r X hL hprod hrough v hv hnv hcon (e*j) (mul_ne_zero he hj) hen u hu
  have hid := fullStructuredPrimeSum_residual R 1 j v 1 1 e u (W r) X
  have hid' : fullStructuredPrimeSum R (v*j^3) 1 1 e u (W r) X =
      fullStructuredPrimeSum R v 1 1 (e*j) u (W r) X := by
    simpa only [one_mul,mul_one,one_pow] using hid
  rwa [hid']

end CubicFirstMoment

end

end OAI
