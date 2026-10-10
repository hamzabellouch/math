import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightPeriodicMass

namespace OAI

/-! # High-weight decay for the original smoothed density waves -/

namespace Ostmann

open Filter
open scoped BigOperators ComplexConjugate SchwartzMap

theorem densityWave_pair_norm_le {p q : ℕ} [NeZero p] [NeZero q]
    (g : ZMod p → ℂ) (h : ZMod q → ℂ) (a : (ZMod p)ˣ) (b : (ZMod q)ˣ)
    (Φ Ψ : 𝓢(ℝ, ℂ)) (α β Y Z : ℝ) (n : ℕ) :
    ‖densityWave g a Φ α Y n * conj (densityWave h b Ψ β Z n)‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 Φ * SchwartzMap.seminorm ℝ 0 0 Ψ) *
        ‖g ((a : ZMod p) * n) * conj (h ((b : ZMod q) * n))‖ := by
  simp only [densityWave, norm_mul, Complex.norm_conj, norm_pow,
    norm_realAdditivePhase, one_pow, mul_one]
  calc
    _ = (‖Φ ((n : ℝ) / Y)‖ * ‖Ψ ((n : ℝ) / Z)‖) *
        (‖g ((a : ZMod p) * n)‖ * ‖h ((b : ZMod q) * n)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul (Φ.norm_le_seminorm ℝ _) (Ψ.norm_le_seminorm ℝ _)
        (norm_nonneg _) (by positivity)) (by positivity)

theorem eventual_high_weight_density_wave (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (U V : Finset ℕ)
      (hpU : ∀ p ∈ U, p.Prime) (hpV : ∀ p ∈ V, p.Prime)
      (N : ℕ) (S : Finset ℕ) (u : ℝ),
      2 * (U ∪ V).toList.prod ^ 2 ≤ N → (2 * N : ℝ) ≤ Real.exp (C * T) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, (U ∪ V).toList.prod.Coprime s) →
      2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      (∀ s ∈ S, Real.exp (T ^ (9999999 / 10000000 : ℝ) / 200) < u ^ s.primeFactors.card) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (a : (ZMod U.toList.prod)ˣ) (b : (ZMod V.toList.prod)ˣ)
        (Φ Ψ : 𝓢(ℝ, ℂ)) (α β Y Z : ℝ),
      let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime U hpU)).ne'⟩
      let : NeZero V.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime V hpV)).ne'⟩
      ‖∑ s ∈ S, (u ^ s.primeFactors.card : ℂ) *
        (densityWave (densityFourier
          (densityCRTList U.toList (primeSet_list_prime U hpU) (primeSet_list_coprime U hpU) D).value)
          a Φ α Y s *
        conj (densityWave (densityFourier
          (densityCRTList V.toList (primeSet_list_prime V hpV) (primeSet_list_coprime V hpV) D).value)
          b Ψ β Z s))‖ ≤
        (SchwartzMap.seminorm ℝ 0 0 Φ * SchwartzMap.seminorm ℝ 0 0 Ψ) *
          (N * Real.exp (-10 * T ^ (9999999 / 10000000 : ℝ))) := by
  filter_upwards [eventual_high_weight_periodic_mass C] with T hT
  intro U V hpU hpV N S u hsize hcut hS hrange hcop hu huU hhigh D a b Φ Ψ α β Y Z _ _
  let hpUV : ∀ p ∈ U ∪ V, p.Prime := fun p hp =>
    (Finset.mem_union.mp hp).elim (hpU p) (hpV p)
  let : NeZero (U ∪ V).toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime _ hpUV)).ne'⟩
  let g := densityFourier
    (densityCRTList U.toList (primeSet_list_prime U hpU) (primeSet_list_coprime U hpU) D).value
  let h := densityFourier
    (densityCRTList V.toList (primeSet_list_prime V hpV) (primeSet_list_coprime V hpV) D).value
  obtain ⟨F, hF, hmass⟩ := primeSet_density_correlation_mass_model U V hpU hpV D a b
  have he (s : ℕ) : g ((a : ZMod U.toList.prod) * s) *
      conj (h ((b : ZMod V.toList.prod) * s)) = F (s : ZMod (U ∪ V).toList.prod) := by
    simpa only [Int.cast_natCast] using hF (s : ℤ)
  have hdecay := hT N (U ∪ V).toList.prod S u (prime_list_prod_pos _ (primeSet_list_prime _ hpUV))
    hsize hcut hS hrange hcop hu huU hhigh F hmass
  have hu0 : 0 ≤ u := by linarith
  let B := SchwartzMap.seminorm ℝ 0 0 Φ * SchwartzMap.seminorm ℝ 0 0 Ψ
  change ‖∑ s ∈ S, (u ^ s.primeFactors.card : ℂ) *
    (densityWave g a Φ α Y s * conj (densityWave h b Ψ β Z s))‖ ≤ _
  calc
    _ ≤ ∑ s ∈ S, ‖(u ^ s.primeFactors.card : ℂ) *
        (densityWave g a Φ α Y s * conj (densityWave h b Ψ β Z s))‖ := norm_sum_le _ _
    _ ≤ ∑ s ∈ S, u ^ s.primeFactors.card * (B * ‖F (s : ZMod (U ∪ V).toList.prod)‖) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [he, B] using densityWave_pair_norm_le g h a b Φ Ψ α β Y Z s
    _ = B * ∑ s ∈ S, u ^ s.primeFactors.card * ‖F (s : ZMod (U ∪ V).toList.prod)‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by dsimp [B]; positivity)

end Ostmann

end OAI
