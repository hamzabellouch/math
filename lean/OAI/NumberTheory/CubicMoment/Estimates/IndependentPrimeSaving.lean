import OAI.NumberTheory.CubicMoment.Estimates.ExcludedLogarithmicPrimeSaving

namespace OAI

/-! Arbitrary logarithmic saving for the genuine independent prime product.
All factors retain the specified varying smooth weights and the exclusion. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
lemma prime_product_log_bound (F : ι → ℂ) (X : ι → ℝ) {K L z : ℝ}
    (hK : 0 ≤ K) (hX : ∀ i, 0 ≤ X i) (hprod : (∏ i, X i) = L)
    (hz : 1 ≤ z) (k : ℕ) (hF : ∀ i, ‖F i‖ ≤ K*X i/z^k) :
    ‖∏ i, F i‖ ≤ K^(Fintype.card ι)*L/z^k := by
  have hzp : 0 < z := zero_lt_one.trans_le hz
  have hk : 1 ≤ z^k := one_le_pow₀ hz
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hden : z^k ≤ (z^k)^(Fintype.card ι) := le_self_pow₀ hk (Nat.ne_of_gt hn)
  rw [norm_prod]
  calc
    _ ≤ ∏ i, (K*X i/z^k) := Finset.prod_le_prod₀ (fun i _ => _root_.norm_nonneg _) (fun i _ => hF i)
    _ = K^(Fintype.card ι)*L/(z^k)^(Fintype.card ι) := by
      rw [Finset.prod_div_distrib,Finset.prod_mul_distrib]
      simp only [Finset.prod_const,Finset.card_univ,hprod]
    _ ≤ _ := div_le_div_of_nonneg_left
      (mul_nonneg (pow_nonneg hK _) (hprod ▸ Finset.prod_nonneg (fun i _ => hX i)))
      (pow_pos hzp _) hden

omit [DecidableEq ι] in
theorem independent_prime_product_saving
    (hSW : CubicPrimeSiegelWalfisz) {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    {c d R A : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hR : 1 ≤ R) (hA : 0 < A)
    (k U : ℕ) (hk : 0 < k) :
    ∃ K Y₀ L₀ : ℝ, 0 < K ∧ 1 < Y₀ ∧ ∀ (r : γ) (X : ι → ℝ),
      (∀ i, Y₀ ≤ X i) → L₀ ≤ L r → 1 ≤ Real.log (L r) →
      (∏ i, X i) = L r → (∀ i, (L r)^c ≤ X i) →
      ∀ q₁ q₂ : Eisenstein, primary q₁ → primary q₂ → Squarefree q₁ → Squarefree q₂ →
      IsCoprime q₁ q₂ → MixedCubicNonprincipal q₁ q₂ →
      (∀ i, norm (q₁*q₂) ≤ (Real.log (X i))^A) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ (L r)^d → ∀ u : ℝ,
      |u| ≤ (1+Real.log (L r))^U →
      ‖∏ i, excludedSmoothPrimeCharacterSum R (X i) (W r i) (mixedCubic q₁ q₂) e u‖ ≤
        K*L r/(1+Real.log (L r))^k := by
  obtain ⟨K,Y₀,L₀,hK,hY₀,hbound⟩ := excluded_logarithmic_prime_saving hSW hW
    (fun z => hlo z.1 z.2) hc hd hR hA k U hk
  refine ⟨K^(Fintype.card ι),Y₀,L₀,pow_pos hK _,hY₀,?_⟩
  intro r X hX hL hlog hprod hrough q₁ q₂ h₁ h₂ hs₁ hs₂ hcop hnon hcon e he heL u hu
  apply prime_product_log_bound _ X hK.le (fun i => (zero_lt_one.trans (hY₀.trans_le (hX i))).le)
    hprod (by linarith) k
  intro i
  exact hbound (r,i) (X i) (hX i) hL hlog (hrough i) q₁ q₂ h₁ h₂ hs₁ hs₂ hcop hnon
    (hcon i) e he heL u hu

end CubicFirstMoment

end

end OAI
