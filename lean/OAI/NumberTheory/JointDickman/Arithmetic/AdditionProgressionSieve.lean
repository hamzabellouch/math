import OAI.NumberTheory.JointDickman.Arithmetic.AdditionSieveGeometry

namespace OAI

/-! # Applying the harmonic sieve to the actual addition progression -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem addition_progression_harmonic_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {κ g ε : ℝ} (hκ : 0 < κ) (hg : 0 < g) (hg1 : g < 1) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (e j b z₀ : ℕ) (c₀ : ℤ) (q W : ℝ) (u v : ℕ),
        0 < e → 0 < b → 0 < j → j ≤ auxiliaryCutoff B →
        (e*b : ℕ) ≤ Real.exp (κ*B) → (e : ℤ)*z₀ = b+(j : ℤ)*c₀ →
        0 ≤ q → q ≤ 1 → 0 < W → u ≤ v →
        (∀ n ∈ Ico u v, W ≤ (z₀ : ℝ)+(j : ℝ)*n) →
        (∑ n ∈ Ico u v, (∏ p ∈ primePrefix B g (auxiliaryPrimes B) \ additionExcludedPrimes B e b,
          residueWeight q 0 ((z₀ : ZMod p)+j*n)*residueWeight (1/2) 0 ((c₀ : ZMod p)+e*n))/
            ((z₀ : ℝ)+(j : ℝ)*n)) ≤
          K*((v : ℝ)-u)/W*Real.exp ((-(3/2-q)*g+ε)*auxiliaryLogLength B)+
            2*(numericAdditionSieveCutoff B g+1 : ℝ)*(numericAdditionSieveCutoff B g : ℝ)^2/W := by
  obtain ⟨K,hK,hbound⟩ := numeric_prefix_harmonic_bound hFord hM hκ hg hg1 hε
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with B hB
  intro e j b z₀ c₀ q W u v he hb hj hcut hsize hbase hq hq1 hW huv hden
  have hE : additionExcludedPrimes B e b ⊆ auxiliaryPrimes B := additionExcludedPrimes_subset B e b
  have hEsize : (∏ p ∈ additionExcludedPrimes B e b, p : ℕ) ≤ Real.exp (κ*B) :=
    (show ((∏ p ∈ additionExcludedPrimes B e b, p : ℕ) : ℝ) ≤ (e*b : ℕ) by
      exact_mod_cast additionExcludedPrimes_product_le he hb).trans hsize
  have hgeom := addition_progression_good_primes (g := g) he hb hj hcut hbase
  have hh := hB (additionExcludedPrimes B e b) z₀ j c₀ e q W u v hE hEsize hq hq1 hW huv
    (by simpa only [Int.cast_natCast] using hgeom)
    (by simpa only [Int.cast_natCast] using hden)
  simpa only [Int.cast_natCast] using hh

end JointDickman

end OAI
