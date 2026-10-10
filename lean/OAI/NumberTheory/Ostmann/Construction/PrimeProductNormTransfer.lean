import OAI.NumberTheory.Ostmann.Construction.PrimeProductMoment

namespace OAI

/-! # Taking the even root of the finite prime-product moment bound -/

namespace Ostmann

open scoped BigOperators

/-- This finite inequality keeps the square and nonsquare contributions
separate, so their numerical estimates can be supplied independently. -/
theorem prime_product_family_norm_transfer (hB : PublishedBonamiBound)
    {I : Type*} [Fintype I] (P S R : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hR : ∀ s ∈ S, s.primeFactors ⊆ R)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (U Z k l : ℕ) (hU : ∀ s ∈ S, s ≤ U) (hZ : ∀ p ∈ P, p ≤ Z)
    (hl : 0 < l) (hk : 1 ≤ k) (hsize : 2 * k ^ 2 ≤ P.card)
    (b : I → S → ℂ) (pick : ℕ → I) (E A B δ : ℝ)
    (hE : 0 ≤ E) (hB0 : 0 ≤ B) (hδ : 0 ≤ δ)
    (henergy : ∀ i, (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b i s‖ ^ 2) ≤ E)
    (hmass : ∀ i, (∑ s : S, ‖b i s‖) ≤ A)
    (hsquare : (2 * (k.factorial : ℝ) / (P.card : ℝ) ^ k) *
      ((Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l)) * ((Z ^ k + 1 : ℕ) : ℝ) ≤ B ^ (2 * l))
    (hnonsquare : (2 * (k.factorial : ℝ) / (P.card : ℝ) ^ k) *
      ((Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l)) *
      ((8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) ≤ δ ^ (2 * l)) :
    (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l)) ≤
      (B * Real.sqrt E + δ) ^ (2 * l) := by
  have hm := prime_product_family_moment_bound hB P S R hS hR hP hodd U Z k l hU hZ
    hl hk hsize b pick E A henergy hmass
  have hpow : (Real.sqrt E) ^ (2 * l) = E ^ l := by
    rw [pow_mul, Real.sq_sqrt hE]
  apply hm.trans
  calc
    _ = ((2 * (k.factorial : ℝ) / (P.card : ℝ) ^ k) *
          ((Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l)) * ((Z ^ k + 1 : ℕ) : ℝ)) * E ^ l +
        ((2 * (k.factorial : ℝ) / (P.card : ℝ) ^ k) *
          ((Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l)) *
          ((8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l))) := by ring
    _ ≤ B ^ (2 * l) * E ^ l + δ ^ (2 * l) :=
      add_le_add (mul_le_mul_of_nonneg_right hsquare (pow_nonneg hE _)) hnonsquare
    _ = (B * Real.sqrt E) ^ (2 * l) + δ ^ (2 * l) := by rw [mul_pow, hpow]
    _ ≤ _ := pow_add_pow_le (mul_nonneg hB0 (Real.sqrt_nonneg E)) hδ (by omega)

end Ostmann

end OAI
