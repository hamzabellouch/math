import OAI.Combinatorics.BalancedRyser.Profiles.ProfileHypergeometric

namespace OAI

namespace Balanced.ProfileTargetExclusion

theorem fraction_error (d N : ℕ) (hN : 2 ≤ N) (hd : d ≤ N) :
    |((d - 1 : ℕ) : ℝ) / (N - 1 : ℕ) - (d : ℝ) / N| ≤
      1 / (N - 1 : ℕ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNm : (0 : ℝ) < (N : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rw [Nat.cast_sub (show 1 ≤ N by omega), Nat.cast_one]
  by_cases hd0 : d = 0
  · subst d
    simp only [Nat.zero_sub, Nat.cast_zero, zero_div, sub_self, abs_zero]
    positivity
  have hd1 : 1 ≤ d := by omega
  rw [Nat.cast_sub hd1, Nat.cast_one]
  have hdN : (d : ℝ) ≤ N := by exact_mod_cast hd
  have hratio : ((d : ℝ) - 1) / ((N : ℝ) - 1) ≤ (d : ℝ) / N := by
    apply (div_le_div_iff₀ hNm hNpos).2
    nlinarith
  rw [abs_of_nonpos (sub_nonpos.mpr hratio)]
  have hid : -(((d : ℝ) - 1) / ((N : ℝ) - 1) - (d : ℝ) / N) =
      (1 - (d : ℝ) / N) / ((N : ℝ) - 1) := by
    field_simp
    ring
  rw [hid]
  apply div_le_div_of_nonneg_right _ hNm.le
  have : (0 : ℝ) ≤ (d : ℝ) / N := by positivity
  linarith

theorem power_error (x y : ℝ) (r : ℕ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    |x ^ r - y ^ r| ≤ (r : ℝ) * |x - y| := by
  have h := Balanced.abs_prod_sub_prod_le_sum_errors (Finset.range r)
    (fun _ => x) (fun _ => y) (fun _ _ => hx) (fun _ _ => hy)
  simpa only [Finset.prod_const, Finset.card_range, Finset.sum_const, nsmul_eq_mul] using h

theorem monomial_error (x x' y y' : ℝ) (a b : ℕ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hx' : 0 ≤ x' ∧ x' ≤ 1)
    (hy : 0 ≤ y ∧ y ≤ 1) (hy' : 0 ≤ y' ∧ y' ≤ 1) :
    |x ^ a * y ^ b - x' ^ a * y' ^ b| ≤
      (a : ℝ) * |x - x'| + (b : ℝ) * |y - y'| := by
  apply (Balanced.abs_mul_sub_mul_le_errors
    ⟨pow_nonneg hy.1 _, pow_le_one₀ hy.1 hy.2⟩
    ⟨pow_nonneg hx'.1 _, pow_le_one₀ hx'.1 hx'.2⟩).trans
  exact add_le_add (power_error x x' a hx hx') (power_error y y' b hy hy')

theorem weighted_parameter_error {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (a b : ι → ℕ) (x x' y y' ε M : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hmean : ∑ i ∈ s, w i * ((a i + b i : ℕ) : ℝ) ≤ M)
    (hx : 0 ≤ x ∧ x ≤ 1) (hx' : 0 ≤ x' ∧ x' ≤ 1)
    (hy : 0 ≤ y ∧ y ≤ 1) (hy' : 0 ≤ y' ∧ y' ≤ 1)
    (hε : 0 ≤ ε) (hex : |x - x'| ≤ ε) (hey : |y - y'| ≤ ε) :
    |(∑ i ∈ s, w i * (x ^ a i * y ^ b i)) -
      ∑ i ∈ s, w i * (x' ^ a i * y' ^ b i)| ≤ M * ε := by
  calc
    |(∑ i ∈ s, w i * (x ^ a i * y ^ b i)) -
        ∑ i ∈ s, w i * (x' ^ a i * y' ^ b i)| =
        |∑ i ∈ s, w i * (x ^ a i * y ^ b i - x' ^ a i * y' ^ b i)| := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ s, |w i * (x ^ a i * y ^ b i - x' ^ a i * y' ^ b i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, w i * (((a i + b i : ℕ) : ℝ) * ε) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i hi)]
      apply mul_le_mul_of_nonneg_left _ (hw i hi)
      apply (monomial_error x x' y y' (a i) (b i) hx hx' hy hy').trans
      rw [Nat.cast_add, add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hex (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hey (Nat.cast_nonneg _))
    _ = (∑ i ∈ s, w i * ((a i + b i : ℕ) : ℝ)) * ε := by
      simp only [← mul_assoc, Finset.sum_mul]
    _ ≤ M * ε := mul_le_mul_of_nonneg_right hmean hε

theorem fraction_bounds (d N : ℕ) (hd : d ≤ N) :
    0 ≤ (d : ℝ) / N ∧ (d : ℝ) / N ≤ 1 := by
  refine ⟨by positivity, ?_⟩
  by_cases hN : N = 0
  · simp [hN]
  have hpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  exact (div_le_one hpos).2 (by exact_mod_cast hd)

theorem weighted_exclusion_error {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (a b : ι → ℕ) (d N : ℕ) (y M : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hmean : ∑ i ∈ s, w i * ((a i + b i : ℕ) : ℝ) ≤ M)
    (hN : 2 ≤ N) (hd : d ≤ N) (hy : 0 ≤ y ∧ y ≤ 1) :
    |(∑ i ∈ s, w i * ((((d - 1 : ℕ) : ℝ) / (N - 1 : ℕ)) ^ a i * y ^ b i)) -
      ∑ i ∈ s, w i * (((d : ℝ) / N) ^ a i * y ^ b i)| ≤
        M / (N - 1 : ℕ) := by
  have h := weighted_parameter_error s w a b
    (((d - 1 : ℕ) : ℝ) / (N - 1 : ℕ)) ((d : ℝ) / N) y y
    (1 / (N - 1 : ℕ)) M hw hmean
    (fraction_bounds (d - 1) (N - 1) (Nat.sub_le_sub_right hd 1))
    (fraction_bounds d N hd) hy hy (by positivity) (fraction_error d N hN hd)
    (by simp)
  simpa only [mul_one_div] using h

theorem weighted_target_hypergeometric_error {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (a b : ι → ℕ)
    (d₁ N₁ d₂ N₂ B : ℕ) {M : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * ((a i + b i : ℕ) : ℝ) ≤ M)
    (hd₁ : d₁ ≤ N₁) (hd₂ : d₂ ≤ N₂)
    (hN₁ : 2 ≤ N₁) (hN₂ : 0 < N₂)
    (hlarge₁ : 2 * B ≤ N₁ - 1) (hlarge₂ : 2 * B ≤ N₂) :
    |(∑ i ∈ s, w i *
        ((((d₁ - 1).descFactorial (a i) : ℝ) / ((N₁ - 1).descFactorial (a i) : ℝ)) *
         ((d₂.descFactorial (b i) : ℝ) / (N₂.descFactorial (b i) : ℝ)))) -
      ∑ i ∈ s, w i * (((d₁ : ℝ) / N₁) ^ a i * ((d₂ : ℝ) / N₂) ^ b i)| ≤
      (2 * (B : ℝ) ^ 2 / (N₁ - 1 : ℕ) + 2 * (B : ℝ) ^ 2 / N₂) +
        M / (B + 1 : ℝ) + M / (N₁ - 1 : ℕ) := by
  have hApprox := Balanced.weighted_two_descFactorial_factors_error s w a b
    (d₁ - 1) (N₁ - 1) d₂ N₂ B hw hsum hmean
    (Nat.sub_le_sub_right hd₁ 1) hd₂ (by omega) hN₂ hlarge₁ hlarge₂
  have hExclude := weighted_exclusion_error s w a b d₁ N₁ ((d₂ : ℝ) / N₂) M
    hw hmean hN₁ hd₁ (fraction_bounds d₂ N₂ hd₂)
  exact (abs_sub_le _ _ _).trans (add_le_add hApprox hExclude)

theorem uniform_target_hypergeometric_approximation (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ {ι : Type*}
      (s : Finset ι) (w : ι → ℝ) (a b : ι → ℕ) (d₁ N₁ d₂ N₂ : ℕ),
      N₀ ≤ N₁ → N₀ ≤ N₂ → d₁ ≤ N₁ → d₂ ≤ N₂ →
      (∀ i ∈ s, 0 ≤ w i) → (∑ i ∈ s, w i = 1) →
      (∑ i ∈ s, w i * ((a i + b i : ℕ) : ℝ) ≤ M) →
      |(∑ i ∈ s, w i *
          ((((d₁ - 1).descFactorial (a i) : ℝ) /
              ((N₁ - 1).descFactorial (a i) : ℝ)) *
           ((d₂.descFactorial (b i) : ℝ) / (N₂.descFactorial (b i) : ℝ)))) -
        ∑ i ∈ s, w i * (((d₁ : ℝ) / N₁) ^ a i * ((d₂ : ℝ) / N₂) ^ b i)| < ε := by
  obtain ⟨Nₐ, hNₐ⟩ := Balanced.uniform_weighted_hypergeometric_approximation M (half_pos hε)
  have hlim : Filter.Tendsto (fun n : ℕ => M / (n : ℝ)) Filter.atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop M
  obtain ⟨Nᵦ, hNᵦ⟩ := Filter.eventually_atTop.mp (hlim.eventually_lt_const (half_pos hε))
  refine ⟨max Nₐ Nᵦ + 2, by omega, ?_⟩
  intro ι s w a b d₁ N₁ d₂ N₂ hN₁ hN₂ hd₁ hd₂ hw hsum hmean
  have hshift : Nₐ ≤ N₁ - 1 := by omega
  have hsecond : Nₐ ≤ N₂ := by omega
  have hApprox := hNₐ s w a b (d₁ - 1) (N₁ - 1) d₂ N₂
    hshift hsecond (Nat.sub_le_sub_right hd₁ 1) hd₂ hw hsum hmean
  have hExclude := weighted_exclusion_error s w a b d₁ N₁ ((d₂ : ℝ) / N₂) M
    hw hmean (by omega) hd₁ (fraction_bounds d₂ N₂ hd₂)
  have hSmall := hNᵦ (N₁ - 1) (by omega)
  have hsumerror := add_lt_add hApprox (hExclude.trans_lt hSmall)
  have htriangle := (abs_sub_le _ _ _).trans_lt hsumerror
  simpa only [add_halves] using htriangle

theorem uniform_target_hypergeometric_approximation_one_population
    (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ {ι : Type*}
      (s : Finset ι) (w : ι → ℝ) (a : ι → ℕ) (d N : ℕ),
      N₀ ≤ N → d ≤ N → (∀ i ∈ s, 0 ≤ w i) →
      (∑ i ∈ s, w i = 1) → (∑ i ∈ s, w i * (a i : ℝ) ≤ M) →
      |(∑ i ∈ s, w i *
          (((d - 1).descFactorial (a i) : ℝ) / ((N - 1).descFactorial (a i) : ℝ))) -
        ∑ i ∈ s, w i * (((d : ℝ) / N) ^ a i)| < ε := by
  obtain ⟨N₀, hN₀, happrox⟩ := uniform_target_hypergeometric_approximation M hε
  refine ⟨N₀, hN₀, ?_⟩
  intro ι s w a d N hN hd hw hsum hmean
  have h := happrox s w a (fun _ => 0) d N 0 N hN hN hd (Nat.zero_le _)
    hw hsum (by simpa only [Nat.add_zero] using hmean)
  simpa only [Nat.descFactorial_zero, Nat.cast_one, div_self one_ne_zero,
    pow_zero, mul_one] using h

end Balanced.ProfileTargetExclusion

end OAI
