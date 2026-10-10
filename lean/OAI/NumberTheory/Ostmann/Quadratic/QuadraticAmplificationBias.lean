import OAI.NumberTheory.Ostmann.Quadratic.QuadraticAmplificationIdentity

namespace OAI

/-! # A fixed quadratic bias produces a large shared coefficient test -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def quadraticPrimeMean (P : Finset ℕ) (e : ℕ → ℂ) (u : ℤ) : ℂ :=
  (∑ p ∈ P, e p * (jacobiSym u p : ℂ)) / (P.card : ℂ)

noncomputable def quadraticAmplifiedCoefficients (P : Finset ℕ) (k : ℕ)
    (e : ℕ → ℂ) : ℕ → ℂ :=
  primeSubsetCoefficient P k (((k.factorial : ℝ) / (P.card : ℝ) ^ k : ℝ) : ℂ) e

theorem norm_jacobi_complex_le (u : ℤ) (p : ℕ) : ‖(jacobiSym u p : ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy u p with h | h | h <;> simp [h]

theorem quadraticAmplifiedCoefficients_identity (P : Finset ℕ) (k Z : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p) (hZ : ∀ p ∈ P, p ≤ Z)
    (e : ℕ → ℂ) (u : ℤ) :
    quadraticTransposeSum (Z ^ k) (quadraticAmplifiedCoefficients P k e) u =
      (∑ f : Fin k ↪ P, ∏ i, e (f i) * (jacobiSym u (f i) : ℂ)) / (P.card : ℂ) ^ k := by
  unfold quadraticAmplifiedCoefficients
  rw [quadratic_amplification_identity P k Z hP hodd hZ]
  have h := distinct_tuple_sum k (fun p : P => e p * (jacobiSym u p : ℂ))
  rw [subset_product_sum_subtype P k (fun p : ℕ => e p * (jacobiSym u p : ℂ))] at h
  rw [h]
  push_cast
  ring

theorem quadratic_amplification_error (P : Finset ℕ) (k Z : ℕ) (hk : 1 ≤ k)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p) (hZ : ∀ p ∈ P, p ≤ Z)
    (e : ℕ → ℂ) (he : ∀ p ∈ P, ‖e p‖ ≤ 1) (hcard : 0 < P.card) (u : ℤ) :
    ‖quadraticPrimeMean P e u ^ k -
      quadraticTransposeSum (Z ^ k) (quadraticAmplifiedCoefficients P k e) u‖ ≤
        (k : ℝ) ^ 2 / P.card := by
  rw [quadraticAmplifiedCoefficients_identity P k Z hP hodd hZ]
  have hy (p : P) : ‖e p * (jacobiSym u p : ℂ)‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (he p p.property) (norm_jacobi_complex_le u p)
      (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
  have h := normalized_distinct_product_error k hk
    (fun p : P => e p * (jacobiSym u p : ℂ)) hy (by simpa using hcard)
  rw [Finset.sum_coe_sort P (fun p : ℕ => e p * (jacobiSym u p : ℂ))] at h
  simpa only [quadraticPrimeMean, Fintype.card_coe] using h

theorem quadratic_amplification_lower (P : Finset ℕ) (k Z : ℕ) (hk : 1 ≤ k)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p) (hZ : ∀ p ∈ P, p ≤ Z)
    (e : ℕ → ℂ) (he : ∀ p ∈ P, ‖e p‖ ≤ 1) (hcard : 0 < P.card)
    (u : ℤ) (c : ℝ) (hc : 0 ≤ c) (hbias : c ≤ ‖quadraticPrimeMean P e u‖) :
    c ^ k - (k : ℝ) ^ 2 / P.card ≤
      ‖quadraticTransposeSum (Z ^ k) (quadraticAmplifiedCoefficients P k e) u‖ := by
  have herr := quadratic_amplification_error P k Z hk hP hodd hZ e he hcard u
  have hpow := pow_le_pow_left₀ hc hbias k
  have ht := norm_add_le
    (quadraticPrimeMean P e u ^ k - quadraticTransposeSum (Z ^ k) (quadraticAmplifiedCoefficients P k e) u)
    (quadraticTransposeSum (Z ^ k) (quadraticAmplifiedCoefficients P k e) u)
  rw [sub_add_cancel, norm_pow] at ht
  linarith

end Ostmann

end OAI
