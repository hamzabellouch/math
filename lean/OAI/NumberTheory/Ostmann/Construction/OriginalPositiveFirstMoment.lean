import OAI.NumberTheory.Ostmann.Characters.PhysicalTuplePoisson
import OAI.NumberTheory.Ostmann.Construction.DistinctMomentAverage
import OAI.NumberTheory.Ostmann.Construction.PrimeTupleAverages
import OAI.NumberTheory.Ostmann.Construction.OriginalAmplifiedMoment
import OAI.NumberTheory.Ostmann.Construction.PrimeProductTranslations

namespace OAI

/-! # First moment of the original positive-frequency statistic -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate
open Filter

noncomputable def originalPrimeProductStatistic (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (N : ℕ) (τ : ℕ → ℤ) (h₀ : ℕ → ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (M : ℕ) : ℝ :=
  ‖originalPositiveFourier Q hQ D M N (h₀ M) ((τ M : ℝ) / M) ((M : ℝ) / X) (𝓕 ψ)‖

theorem physical_positive_first_mean (Q P : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (X H : ℝ) (hX : 0 < X) (hH : 0 ≤ H)
    (ε : ℕ → ℝ) (hε : ∀ p ∈ P, ε p = 1 ∨ ε p = -1) (t : ℕ → ℤ)
    (k N : ℕ) (hk : 0 < k) (hkP : k ≤ P.card) (hK : 3000 ≤ (Q.card : ℝ))
    (τ : ℕ → ℤ) (h₀ : ℕ → ℕ)
    (hdata : ∀ e : Fin k ↪ P,
      Q.toList.prod.Coprime (primeTupleProduct P e) ∧
      H * ((primeTupleProduct P e : ℝ) / X) * Q.toList.prod ≤ N ∧
      0 ≤ τ (primeTupleProduct P e) ∧ τ (primeTupleProduct P e) < primeTupleProduct P e ∧
      (∀ i, (τ (primeTupleProduct P e) : ZMod (e i).val) = (t (e i).val : ZMod (e i).val)) ∧
      (Q.toList.prod : ℤ) ∣ τ (primeTupleProduct P e) +
        (primeTupleProduct P e : ℤ) * h₀ (primeTupleProduct P e))
    (hsupp : ∀ x : ℝ, H < x → 𝓕 ψ x = 0)
    (hlower : Real.sqrt X * Real.exp ((2 / 125 : ℝ) * Q.card) / 2 ≤
      ∑' n : ℤ, physicalWeight Q D ψ X n *
        ternaryDistinctMean (fun p : P => orientedQuadraticValue ε t n p) k) :
    Real.exp ((3 / 200 : ℝ) * Q.card) ≤
      (P.card.choose k : ℝ)⁻¹ * ∑ m ∈ primeSubsetProducts P k,
        originalPrimeProductStatistic Q hQ D N τ h₀ ψ X m := by
  have hb (e : Fin k ↪ P) :
      |∑' n : ℤ, physicalWeight Q D ψ X n * ∏ i, orientedQuadraticValue ε t n (e i).val| ≤
      2 * Real.sqrt X * originalPrimeProductStatistic Q hQ D N τ h₀ ψ X (primeTupleProduct P e) := by
    obtain ⟨hc, hcut, ht0, htlt, ht, hl⟩ := hdata e
    exact physical_tuple_positive_bound Q P hQ hP hodd D ψ hreal X H hX hH ε hε t hk e hc
      N (h₀ (primeTupleProduct P e)) hcut hsupp (τ (primeTupleProduct P e)) ht0 htlt ht hl
  have hm := amplified_distinct_first_mean (physicalWeight Q D ψ X)
    (fun n (p : P) => orientedQuadraticValue ε t n p)
    (physicalWeight_nonneg Q hQ D ψ hψ0 X)
    (fun n p => by
      rcases orientedQuadraticValue_ternary ε t n p (hε p p.property) with h | h | h <;>
        rw [h] <;> norm_num)
    (physicalWeight_summable Q hQ D ψ X hX) k
    (fun e : Fin k ↪ P => originalPrimeProductStatistic Q hQ D N τ h₀ ψ X (primeTupleProduct P e))
    X Q.card hX hK (fun _ => norm_nonneg _) (by simpa using hkP) hb hlower
  rwa [primeTuple_uniform_mean P hP k] at hm

/-- The phase table in the first-moment bound is constructed by CRT and is
indexed by products, so it is compatible with the fixed coefficient moments. -/
theorem exists_positive_first_mean (Q P : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (X H : ℝ) (hX : 0 < X) (hH : 0 ≤ H)
    (ε : ℕ → ℝ) (hε : ∀ p ∈ P, ε p = 1 ∨ ε p = -1) (t : ℕ → ℤ)
    (k N : ℕ) (hk : 0 < k) (hkP : k ≤ P.card) (hK : 3000 ≤ (Q.card : ℝ))
    (hcop : ∀ M ∈ primeSubsetProducts P k, Q.toList.prod.Coprime M)
    (hcut : ∀ M ∈ primeSubsetProducts P k, H * ((M : ℝ) / X) * Q.toList.prod ≤ N)
    (hsupp : ∀ x : ℝ, H < x → 𝓕 ψ x = 0)
    (hlower : Real.sqrt X * Real.exp ((2 / 125 : ℝ) * Q.card) / 2 ≤
      ∑' n : ℤ, physicalWeight Q D ψ X n *
        ternaryDistinctMean (fun p : P => orientedQuadraticValue ε t n p) k) :
    ∃ τ : ℕ → ℤ, ∃ h₀ : ℕ → ℕ,
      (∀ M ∈ primeSubsetProducts P k,
        0 ≤ τ M ∧ τ M < M ∧ h₀ M < Q.toList.prod ∧
        (Q.toList.prod : ℤ) ∣ τ M + (M : ℤ) * h₀ M ∧
        ∀ p ∈ M.primeFactors, (τ M : ZMod p) = (t p : ZMod p)) ∧
      Real.exp ((3 / 200 : ℝ) * Q.card) ≤
        (P.card.choose k : ℝ)⁻¹ * ∑ m ∈ primeSubsetProducts P k,
          originalPrimeProductStatistic Q hQ D N τ h₀ ψ X m := by
  let : NeZero Q.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime Q hQ)).ne'⟩
  obtain ⟨τ, h₀, hτ⟩ := exists_primeProduct_translations P hP k Q.toList.prod t hcop
  refine ⟨fun M => (τ M : ℤ), h₀, ?_, ?_⟩
  · intro M hM
    obtain ⟨ha, hb, hd, hc⟩ := hτ M hM
    exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr ha, hb, hd, by simpa using hc⟩
  · apply physical_positive_first_mean Q P hQ hP hodd D ψ hreal hψ0 X H hX hH ε hε t
      k N hk hkP hK (fun M => (τ M : ℤ)) h₀ _ hsupp hlower
    intro e
    have he := primeTupleProduct_mem P e
    obtain ⟨ha, hb, hd, hc⟩ := hτ (primeTupleProduct P e) he
    refine ⟨hcop _ he, hcut _ he, Int.natCast_nonneg _, Int.ofNat_lt.mpr ha, ?_, hd⟩
    intro i
    simpa only [Int.cast_natCast] using hc (e i).val (primeTuple_member_primeFactors P hP e i)

/-- The original tail bias and size estimates now imply the Fourier first
moment. There is no assumed Fourier lower bound in this statement. -/
theorem eventual_original_positive_mean (cψ a c C : ℝ)
    (hcψ : 0 < cψ) (ha : 0 < a) (hc : 0 < c) (hC : 1 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q P : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (_hP : ∀ p ∈ P, p.Prime) (_hodd : ∀ p ∈ P, Odd p)
      (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ),
      0 < X → 0 ≤ H → (∀ x, conj (ψ x) = ψ x) → (∀ x, 0 ≤ (ψ x).re) →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re) →
      H < X / Q.toList.prod → (∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) →
      (𝓕 ψ 0).re ≤ C → ∀ (S : Finset ℤ),
      (∀ n ∈ S, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) →
      a * Real.sqrt X / T ^ 6 ≤ (S.card : ℝ) →
      (∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3) →
      (∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p) →
      ∀ (ε : ℕ → ℝ) (t : ℕ → ℤ), (∀ p ∈ P, ε p = 1 ∨ ε p = -1) →
      (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p) →
      ∀ k N : ℕ, 0 < k → Even k → k ≤ P.card →
      (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      3000 ≤ (Q.card : ℝ) → Real.exp T ≤ C * T * P.card → X ≤ Real.exp ((k : ℝ) * T) →
      (∀ M ∈ primeSubsetProducts P k, Q.toList.prod.Coprime M) →
      (∀ M ∈ primeSubsetProducts P k, H * ((M : ℝ) / X) * Q.toList.prod ≤ N) →
      ∃ τ : ℕ → ℤ, ∃ h₀ : ℕ → ℕ,
        (∀ M ∈ primeSubsetProducts P k,
          0 ≤ τ M ∧ τ M < M ∧ h₀ M < Q.toList.prod ∧
          (Q.toList.prod : ℤ) ∣ τ M + (M : ℤ) * h₀ M ∧
          ∀ p ∈ M.primeFactors, (τ M : ZMod p) = (t p : ZMod p)) ∧
        Real.exp ((3 / 200 : ℝ) * Q.card) ≤
          (P.card.choose k : ℝ)⁻¹ * ∑ m ∈ primeSubsetProducts P k,
            originalPrimeProductStatistic Q hQ D N τ h₀ ψ X m := by
  filter_upwards [eventual_original_distinct_moment cψ a c C hcψ ha hc hC] with T hm
  intro Q P hQ hP hodd D ψ X H hX hH0 hreal hψ0 hψ1 hH hsupp hCψ S hS hcard hD hSD
    ε t hε hbias k N hk heven hkP hkU hK hK3000 hpop hXk hcop hcut
  apply exists_positive_first_mean Q P hQ hP hodd D ψ hreal hψ0 X H hX hH0 ε hε t
    k N hk hkP hK3000 hcop hcut
  · intro x hx
    exact hsupp x (by rwa [abs_of_nonneg (hH0.trans hx.le)])
  · exact hm Q P hQ D ψ X H hX hψ0 hψ1 hH hsupp hCψ S hS hcard hD hSD
      ε t hε hbias k hk heven hkP hkU hK hpop hXk

end Ostmann

end OAI
