import OAI.Combinatorics.BalancedRyser.Probability.HypergeometricApproximation

namespace OAI

namespace Balanced
open scoped _root_.Balanced

theorem weighted_profile_error_of_mean_bound {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (height : ι → ℕ) (f g : ι → ℝ)
    (B : ℕ) {ε M : ℝ} (hε : 0 ≤ ε)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * (height i : ℝ) ≤ M)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1)
    (hg : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ 1)
    (hsmall : ∀ i ∈ s, height i ≤ B → |f i - g i| ≤ ε) :
    |(∑ i ∈ s, w i * f i) - ∑ i ∈ s, w i * g i| ≤
      ε + M / (B + 1 : ℝ) := by
  have hden : (0 : ℝ) < B + 1 := by positivity
  have hpoint (i : ι) (hi : i ∈ s) :
      |f i - g i| ≤ ε + (height i : ℝ) / (B + 1 : ℝ) := by
    by_cases hBi : height i ≤ B
    · have h := hsmall i hi hBi
      have hnonneg : (0 : ℝ) ≤ (height i : ℝ) / (B + 1 : ℝ) := by positivity
      linarith
    · have hlarge : (B + 1 : ℝ) ≤ height i := by exact_mod_cast (show B + 1 ≤ height i by omega)
      have htail : (1 : ℝ) ≤ (height i : ℝ) / (B + 1 : ℝ) := by
        apply (le_div_iff₀ hden).2
        simpa using hlarge
      have habs : |f i - g i| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [(hf i hi).1, (hf i hi).2, (hg i hi).1, (hg i hi).2]
      linarith
  calc
    |(∑ i ∈ s, w i * f i) - ∑ i ∈ s, w i * g i|
        = |∑ i ∈ s, w i * (f i - g i)| := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ s, |w i * (f i - g i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, w i * |f i - g i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i hi)]
    _ ≤ ∑ i ∈ s, w i * (ε + (height i : ℝ) / (B + 1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hpoint i hi) (hw i hi)
    _ = ε + (∑ i ∈ s, w i * (height i : ℝ)) / (B + 1 : ℝ) := by
      simp_rw [mul_add]
      simp only [← mul_div_assoc]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul, Finset.sum_div]
    _ ≤ ε + M / (B + 1 : ℝ) :=
      by linarith [div_le_div_of_nonneg_right hmean hden.le]

theorem descFactorial_ratio_bounds (d N r : ℕ) (hd : d ≤ N) :
    0 ≤ (d.descFactorial r : ℝ) / (N.descFactorial r : ℝ) ∧
      (d.descFactorial r : ℝ) / (N.descFactorial r : ℝ) ≤ 1 := by
  refine ⟨by positivity, ?_⟩
  by_cases hzero : N.descFactorial r = 0
  · simp [hzero]
  · have hpos : (0 : ℝ) < N.descFactorial r := by exact_mod_cast Nat.pos_of_ne_zero hzero
    apply (div_le_one hpos).2
    exact_mod_cast Nat.descFactorial_le r hd

theorem abs_mul_sub_mul_le_errors {a b c d : ℝ}
    (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) :
    |a * b - c * d| ≤ |a - c| + |b - d| := by
  calc
    |a * b - c * d| = |(a - c) * b + c * (b - d)| := by congr 1; ring
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = |a - c| * b + c * |b - d| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hb.1, abs_of_nonneg hc.1]
    _ ≤ |a - c| + |b - d| := by nlinarith [abs_nonneg (a - c), abs_nonneg (b - d)]

theorem two_descFactorial_factors_error (d₁ N₁ d₂ N₂ r₁ r₂ B : ℕ)
    (hd₁ : d₁ ≤ N₁) (hd₂ : d₂ ≤ N₂) (hr₁ : r₁ ≤ B) (hr₂ : r₂ ≤ B)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hlarge₁ : 2 * B ≤ N₁) (hlarge₂ : 2 * B ≤ N₂) :
    |((d₁.descFactorial r₁ : ℝ) / (N₁.descFactorial r₁ : ℝ)) *
        ((d₂.descFactorial r₂ : ℝ) / (N₂.descFactorial r₂ : ℝ)) -
      ((d₁ : ℝ) / N₁) ^ r₁ * ((d₂ : ℝ) / N₂) ^ r₂| ≤
      2 * (B : ℝ) ^ 2 / N₁ + 2 * (B : ℝ) ^ 2 / N₂ := by
  have hratio : 0 ≤ ((d₁ : ℝ) / N₁) ^ r₁ ∧ ((d₁ : ℝ) / N₁) ^ r₁ ≤ 1 := by
    have hpos : (0 : ℝ) < N₁ := by exact_mod_cast hN₁
    have hbase : (d₁ : ℝ) / N₁ ≤ 1 := (div_le_one hpos).2 (by exact_mod_cast hd₁)
    exact ⟨by positivity, pow_le_one₀ (by positivity) hbase⟩
  have h := abs_mul_sub_mul_le_errors (a := (d₁.descFactorial r₁ : ℝ) / (N₁.descFactorial r₁ : ℝ))
    (d := ((d₂ : ℝ) / N₂) ^ r₂) (descFactorial_ratio_bounds d₂ N₂ r₂ hd₂) hratio
  exact h.trans (add_le_add
    (descFactorial_ratio_power_error_uniform d₁ N₁ r₁ B hd₁ hr₁ hN₁ hlarge₁)
    (descFactorial_ratio_power_error_uniform d₂ N₂ r₂ B hd₂ hr₂ hN₂ hlarge₂))

theorem weighted_two_descFactorial_factors_error {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (a b : ι → ℕ)
    (d₁ N₁ d₂ N₂ B : ℕ) {M : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * ((a i + b i : ℕ) : ℝ) ≤ M)
    (hd₁ : d₁ ≤ N₁) (hd₂ : d₂ ≤ N₂)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hlarge₁ : 2 * B ≤ N₁) (hlarge₂ : 2 * B ≤ N₂) :
    |(∑ i ∈ s, w i *
        (((d₁.descFactorial (a i) : ℝ) / (N₁.descFactorial (a i) : ℝ)) *
         ((d₂.descFactorial (b i) : ℝ) / (N₂.descFactorial (b i) : ℝ)))) -
      ∑ i ∈ s, w i * (((d₁ : ℝ) / N₁) ^ (a i) * ((d₂ : ℝ) / N₂) ^ (b i))| ≤
      (2 * (B : ℝ) ^ 2 / N₁ + 2 * (B : ℝ) ^ 2 / N₂) + M / (B + 1 : ℝ) := by
  apply weighted_profile_error_of_mean_bound s w (fun i => a i + b i) _ _ B
    (by positivity) hw hsum hmean
  · intro i hi
    have h₁ := descFactorial_ratio_bounds d₁ N₁ (a i) hd₁
    have h₂ := descFactorial_ratio_bounds d₂ N₂ (b i) hd₂
    exact ⟨mul_nonneg h₁.1 h₂.1, by nlinarith⟩
  · intro i hi
    have hpos₁ : (0 : ℝ) < N₁ := by exact_mod_cast hN₁
    have hpos₂ : (0 : ℝ) < N₂ := by exact_mod_cast hN₂
    have hbase₁ : (d₁ : ℝ) / N₁ ≤ 1 := (div_le_one hpos₁).2 (by exact_mod_cast hd₁)
    have hbase₂ : (d₂ : ℝ) / N₂ ≤ 1 := (div_le_one hpos₂).2 (by exact_mod_cast hd₂)
    have hpow₁ : ((d₁ : ℝ) / N₁) ^ (a i) ≤ 1 := pow_le_one₀ (by positivity) hbase₁
    have hpow₂ : ((d₂ : ℝ) / N₂) ^ (b i) ≤ 1 := pow_le_one₀ (by positivity) hbase₂
    have hnonneg₁ : 0 ≤ ((d₁ : ℝ) / N₁) ^ (a i) := by positivity
    have hnonneg₂ : 0 ≤ ((d₂ : ℝ) / N₂) ^ (b i) := by positivity
    exact ⟨mul_nonneg hnonneg₁ hnonneg₂, by nlinarith⟩
  · intro i hi hsmall
    exact two_descFactorial_factors_error d₁ N₁ d₂ N₂ (a i) (b i) B hd₁ hd₂
      (by omega) (by omega) hN₁ hN₂ hlarge₁ hlarge₂

theorem exists_profile_approximation_cutoff (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B N₀ : ℕ, 1 ≤ N₀ ∧ 2 * B ≤ N₀ ∧
      ∀ N₁ N₂ : ℕ, N₀ ≤ N₁ → N₀ ≤ N₂ →
        (2 * (B : ℝ) ^ 2 / N₁ + 2 * (B : ℝ) ^ 2 / N₂) +
          M / (B + 1 : ℝ) < ε := by
  have htail : Filter.Tendsto (fun B : ℕ => M / (B + 1 : ℝ)) Filter.atTop (nhds 0) :=
    (Filter.tendsto_atTop_add_const_right Filter.atTop 1
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop M
  obtain ⟨B, hB⟩ := (htail.eventually_lt_const (half_pos hε)).exists
  have hmain : Filter.Tendsto (fun N : ℕ => 4 * (B : ℝ) ^ 2 / N) Filter.atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop (4 * (B : ℝ) ^ 2)
  have hlarge := (Filter.eventually_ge_atTop (1 : ℕ)).and
    ((Filter.eventually_ge_atTop (2 * B)).and (hmain.eventually_lt_const (half_pos hε)))
  obtain ⟨N₀, hN₀, hBN₀, herror⟩ := hlarge.exists
  refine ⟨B, N₀, hN₀, hBN₀, ?_⟩
  intro N₁ N₂ h₁ h₂
  have hpos : (0 : ℝ) < N₀ := by exact_mod_cast (show 0 < N₀ by omega)
  have h₁' : (N₀ : ℝ) ≤ N₁ := by exact_mod_cast h₁
  have h₂' : (N₀ : ℝ) ≤ N₂ := by exact_mod_cast h₂
  have hb₁ : 2 * (B : ℝ) ^ 2 / N₁ ≤ 2 * (B : ℝ) ^ 2 / N₀ :=
    div_le_div_of_nonneg_left (by positivity) hpos h₁'
  have hb₂ : 2 * (B : ℝ) ^ 2 / N₂ ≤ 2 * (B : ℝ) ^ 2 / N₀ :=
    div_le_div_of_nonneg_left (by positivity) hpos h₂'
  have hid : 2 * (B : ℝ) ^ 2 / N₀ + 2 * (B : ℝ) ^ 2 / N₀ =
      4 * (B : ℝ) ^ 2 / N₀ := by ring
  linarith

theorem uniform_weighted_hypergeometric_approximation (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ {ι : Type*} (s : Finset ι) (w : ι → ℝ) (a b : ι → ℕ)
      (d₁ N₁ d₂ N₂ : ℕ),
      N₀ ≤ N₁ → N₀ ≤ N₂ → d₁ ≤ N₁ → d₂ ≤ N₂ →
      (∀ i ∈ s, 0 ≤ w i) → (∑ i ∈ s, w i = 1) →
      (∑ i ∈ s, w i * ((a i + b i : ℕ) : ℝ) ≤ M) →
      |(∑ i ∈ s, w i *
          (((d₁.descFactorial (a i) : ℝ) / (N₁.descFactorial (a i) : ℝ)) *
           ((d₂.descFactorial (b i) : ℝ) / (N₂.descFactorial (b i) : ℝ)))) -
        ∑ i ∈ s, w i * (((d₁ : ℝ) / N₁) ^ (a i) * ((d₂ : ℝ) / N₂) ^ (b i))| < ε := by
  obtain ⟨B, N₀, hN₀, hBN₀, hcut⟩ := exists_profile_approximation_cutoff M hε
  refine ⟨N₀, ?_⟩
  intro ι s w a b d₁ N₁ d₂ N₂ h₁ h₂ hd₁ hd₂ hw hsum hmean
  exact (weighted_two_descFactorial_factors_error s w a b d₁ N₁ d₂ N₂ B
    hw hsum hmean hd₁ hd₂ (by omega) (by omega) (by omega) (by omega)).trans_lt
      (hcut N₁ N₂ h₁ h₂)

end Balanced

end OAI
