import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductSampling

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem sum_primeProductSamples {A : Type*} [AddCommMonoid A]
    {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p) (k : ℕ) (f : ℕ → A) :
    (∑ q ∈ primeProductSamples P k, f q) =
      ∑ U ∈ P.powersetCard k, f (∏ p ∈ U, p) := by
  classical
  let e : P ↪ ℕ := Function.Embedding.subtype (fun p => p ∈ P)
  have he : (Finset.univ : Finset P).map e = P := by
    ext p
    simp [e]
  have hps : P.powersetCard k = ((Finset.univ : Finset P).powersetCard k).map
      (Finset.mapEmbedding e).toEmbedding := by
    rw [← Finset.powersetCard_map, he]
  rw [primeProductSamples, Finset.sum_image]
  · rw [hps, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro U hU
    change f (primeSubsetProduct U) = f (∏ p ∈ U.map e, p)
    rw [Finset.prod_map]
    rfl
  · intro U hU V hV heq
    exact primeSubsetProduct_injective hP heq

theorem factorial_pow_inv_le_choose_inv {J k : ℕ} (hJ : 0 < J) (hk : k ≤ J) :
    (k.factorial : ℝ) / (J : ℝ) ^ k ≤ (Nat.choose J k : ℝ)⁻¹ := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hchoose : (0 : ℝ) < Nat.choose J k := by exact_mod_cast Nat.choose_pos hk
  have h := (Nat.choose_le_pow_div k J : (Nat.choose J k : ℝ) ≤ (J : ℝ) ^ k / k.factorial)
  have hm : (Nat.choose J k : ℝ) * k.factorial ≤ (J : ℝ) ^ k :=
    (le_div_iff₀ hfac).mp h
  apply (div_le_iff₀ (pow_pos hJr k)).mpr
  rw [← div_eq_inv_mul]
  apply (le_div_iff₀ hchoose).mpr
  simpa only [mul_comm] using hm

theorem normalized_subset_sum_le_primeProductMean {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (hJ : 0 < P.card) {k : ℕ} (hk : k ≤ P.card)
    (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q) :
    ((k.factorial : ℝ) / (P.card : ℝ) ^ k) *
      (∑ U ∈ P.powersetCard k, f (∏ p ∈ U, p)) ≤ primeProductMean P k f := by
  rw [← sum_primeProductSamples hP k f]
  unfold primeProductMean
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_right (factorial_pow_inv_le_choose_inv hJ hk)
      (show 0 ≤ ∑ q ∈ primeProductSamples P k, f q from
        Finset.sum_nonneg (fun q hq => hf q))

end Ostmann.QuadraticCenter

end OAI
