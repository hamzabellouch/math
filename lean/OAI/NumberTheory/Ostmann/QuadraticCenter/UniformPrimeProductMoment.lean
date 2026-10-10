import OAI.NumberTheory.Ostmann.Characters.PrimeMomentAsymptotics

namespace OAI

/-! # Uniform finite-family moment bound under the original prime-product law -/

namespace Ostmann

open Filter
open scoped BigOperators

/-- The manuscript's fixed-family estimate. All sampling and numerical
transfer factors are discharged; only Bonami's precisely stated published
inequality is an analytic input to this moment calculation. -/
theorem eventual_uniform_prime_product_moment (hB : PublishedBonamiBound)
    (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ {I : Type*} [Fintype I]
      (P S R : Finset ℕ) (U Z k l : ℕ),
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s.primeFactors ⊆ R) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) →
      (∀ s ∈ S, s ≤ U) → (∀ p ∈ P, p ≤ Z) →
      1 ≤ Z → Real.exp T ≤ C * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (Fintype.card I : ℝ) ≤ Real.exp (C * T) → (U : ℝ) ≤ Real.exp (C * T) →
      ∀ (b : I → S → ℂ) (pick : ℕ → I) (E A : ℝ),
      0 ≤ E → 0 ≤ A → A ≤ Real.exp (C * T) →
      (∀ i, (∑ s : S, ((2 * l : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b i s‖ ^ 2) ≤ E) →
      (∀ i, (∑ s : S, ‖b i s‖) ≤ A) →
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l)) ≤
        (Real.exp (ε * T ^ (9999999 / 10000000 : ℝ)) * Real.sqrt E +
          Real.exp (-10 * T)) ^ (2 * l) := by
  filter_upwards [eventual_prime_moment_factors C ε hC hε] with T hfactor
  intro I _ P S R U Z k l hS hR hP hodd hU hZ hZ1 hpop hZU hk hsize hkL hkU
    hl hlL hlU hI hUU b pick E A hE hA hAA henergy hmass
  have hJ : 0 < P.card := by nlinarith
  obtain ⟨hsquare, hnonsquare⟩ := hfactor P.card Z k l (Fintype.card I) U A
    hJ hZ1 hpop hZU hkL hkU hl hlL hlU hI hUU hA hAA
  have henergy' (i : I) :
      (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b i s‖ ^ 2) ≤ E := by
    apply le_trans (Finset.sum_le_sum (fun s _ => ?_)) (henergy i)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.sub_le (2 * l) 1)) _)
      (sq_nonneg _)
  exact prime_product_family_norm_transfer hB P S R hS hR hP hodd U Z k l hU hZ
    (by omega) hk hsize b pick E A _ _ hE (Real.exp_nonneg _) (Real.exp_nonneg _)
    henergy' hmass hsquare hnonsquare

end Ostmann

end OAI
