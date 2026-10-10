import OAI.NumberTheory.Ostmann.ZeroDensity.HighWeightDensityWave
import OAI.NumberTheory.Ostmann.QuadraticCenter.WeightedQuadraticCorrelation

namespace OAI

/-! # High-weight correlations after the quadratic normalization and pair count -/

namespace Ostmann

open Filter
open scoped BigOperators ComplexConjugate SchwartzMap

theorem eventual_high_weight_quadratic_waves (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (U V : Finset ℕ)
      (hpU : ∀ p ∈ U, p.Prime) (hpV : ∀ p ∈ V, p.Prime)
      (N : ℕ) (S : Finset ℕ) (u : ℝ),
      0 < N → 2 * (U ∪ V).toList.prod ^ 2 ≤ N → (2 * N : ℝ) ≤ Real.exp (C * T) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, (U ∪ V).toList.prod.Coprime s) →
      2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      (∀ s ∈ S, Real.exp (T ^ (9999999 / 10000000 : ℝ) / 200) < u ^ s.primeFactors.card) →
      ∀ {ι κ : Type*} (D : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ι) (W' : Finset κ)
        (a : ι → (ZMod U.toList.prod)ˣ) (b : κ → (ZMod V.toList.prod)ˣ)
        (Φ Ψ : 𝓢(ℝ, ℂ)) (α Y : ι → ℝ) (β Z : κ → ℝ) (R v H : ℝ),
      0 < R → 0 < v →
      (W.card : ℝ) * W'.card ≤ H * R * Real.sqrt ((U.toList.prod : ℝ) * V.toList.prod) / ((N : ℝ) * v) →
      let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime U hpU)).ne'⟩
      let : NeZero V.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime V hpV)).ne'⟩
      ‖∑ s ∈ S, (u ^ s.primeFactors.card : ℂ) *
        (normalizedDensityWaveSum (densityFourier
          (densityCRTList U.toList (primeSet_list_prime U hpU) (primeSet_list_coprime U hpU) D).value)
          W a Φ α Y R v s *
        conj (normalizedDensityWaveSum (densityFourier
          (densityCRTList V.toList (primeSet_list_prime V hpV) (primeSet_list_coprime V hpV) D).value)
          W' b Ψ β Z R v s) / (s : ℂ))‖ ≤
        H * (SchwartzMap.seminorm ℝ 0 0 Φ * SchwartzMap.seminorm ℝ 0 0 Ψ) *
          Real.exp (-10 * T ^ (9999999 / 10000000 : ℝ)) := by
  filter_upwards [eventual_high_weight_density_wave C] with T hT
  intro U V hpU hpV N S u hN hsize hcut hS hrange hcop hu huU hhigh ι κ D W W' a b
    Φ Ψ α Y β Z R v H hR hv hcount _ _
  let g := densityFourier
    (densityCRTList U.toList (primeSet_list_prime U hpU) (primeSet_list_coprime U hpU) D).value
  let h := densityFourier
    (densityCRTList V.toList (primeSet_list_prime V hpV) (primeSet_list_coprime V hpV) D).value
  let B := SchwartzMap.seminorm ℝ 0 0 Φ * SchwartzMap.seminorm ℝ 0 0 Ψ
  let E := Real.exp (-10 * T ^ (9999999 / 10000000 : ℝ))
  have hpair (w : ι) (_hw : w ∈ W) (z : κ) (_hz : z ∈ W') :
      ‖∑ s ∈ S, (u ^ s.primeFactors.card : ℂ) *
        (densityWave g (a w) Φ (α w) (Y w) s *
          conj (densityWave h (b z) Ψ (β z) (Z z) s))‖ ≤ B * ((N : ℝ) * E) :=
    hT U V hpU hpV N S u hsize hcut hS hrange hcop hu huU hhigh D (a w) (b z)
      Φ Ψ (α w) (β z) (Y w) (Z z)
  have hd : (0 : ℝ) < U.toList.prod := by
    exact_mod_cast prime_list_prod_pos _ (primeSet_list_prime U hpU)
  have he : (0 : ℝ) < V.toList.prod := by
    exact_mod_cast prime_list_prod_pos _ (primeSet_list_prime V hpV)
  have hn := weighted_normalized_quadratic_pair_bound S W W' (fun s => (s : ℝ))
    (fun s => (u ^ s.primeFactors.card : ℂ))
    (fun w s => densityWave g (a w) Φ (α w) (Y w) s)
    (fun z s => densityWave h (b z) Ψ (β z) (Z z) s)
    R U.toList.prod V.toList.prod v (B * ((N : ℝ) * E)) hR hd he hv
    (by intro s hs; exact_mod_cast lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp (hrange s hs)).1) hpair
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  change _ ≤ H * B * E
  apply hn.trans
  have hc := quadratic_pair_count_cancellation R U.toList.prod V.toList.prod v N B E H
    hR hd he hv hNR (by dsimp [B]; positivity) (by dsimp [E]; positivity) W.card W'.card hcount
  convert hc using 1
  ring

end Ostmann

end OAI
