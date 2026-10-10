import OAI.NumberTheory.Ostmann.Arithmetic.RangedComplexityBudget
import OAI.NumberTheory.Ostmann.Construction.WordFourierBudgetBounds
import OAI.NumberTheory.Ostmann.Arithmetic.PrimePairDecay
import OAI.NumberTheory.Ostmann.Construction.DyadicShellBudget

namespace OAI

/-! # Explicit numerical costs of the two actual ranged word histories -/

namespace Ostmann
open scoped BigOperators
open Filter

noncomputable def rangedPairExponent (n : ℕ) (b d C S H : ℝ) : ℝ :=
  H + 2 * C * wordPeriodExponent n b +
    4 * Real.log 3 * (((3 * 2 ^ n + 3 * (2 ^ n - 1) : ℕ) : ℝ) + 4 * d) *
      b ^ (n + 1) + 2 * ((4 * S + 2 * C) * (2 ^ n : ℕ))

theorem rangedPairExponent_nonneg (n : ℕ) (b d C S H : ℝ)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hC : 0 ≤ C) (hS : 0 ≤ S) (hH : 0 ≤ H) :
    0 ≤ rangedPairExponent n b d C S H := by
  unfold rangedPairExponent wordPeriodExponent
  positivity

/-- The period, Boolean partition, Fourier variation and harmonic normalizers
all have a common explicit polynomial exponent. -/
theorem ranged_pair_numeric_costs {σ : Type*} {n : ℕ}
    (T T' : WordTransferTemplate σ n) (D D' : WordRangeDecoration σ n)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (ht' : NonzeroInternalFrequencies n t')
    (B V E : ℕ) (f f' : WordFourierParameters n) (P Q : Finset ℕ)
    (b d C S H m : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ d) (hC : 0 ≤ C)
    (hS : 1 ≤ S) (hH : 0 ≤ H) (hm : 0 ≤ m)
    (hB : (B : ℝ) ≤ b * (1 + m))
    (hD : (D.count : ℝ) ≤ d * (1 + m)) (hD' : (D'.count : ℝ) ≤ d * (1 + m))
    (hV : (V : ℝ) ≤ Real.exp (C * (1 + m)))
    (hf : ∀ s ∈ allFrequencyList n t, s.natAbs ≤ V)
    (hf' : ∀ s ∈ allFrequencyList n t', s.natAbs ≤ V)
    (hs₀ : SchwartzMap.seminorm ℝ 0 0 f.profile ≤ S)
    (hs₁ : SchwartzMap.seminorm ℝ 0 1 f.profile ≤ S)
    (hs₀' : SchwartzMap.seminorm ℝ 0 0 f'.profile ≤ S)
    (hs₁' : SchwartzMap.seminorm ℝ 0 1 f'.profile ≤ S)
    (hr : ∀ i, f.upper i - f.lower i ≤ Real.exp (C * (1 + m)))
    (hr' : ∀ i, f'.upper i - f'.lower i ≤ Real.exp (C * (1 + m)))
    (hE : ((Nat.log 2 E + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + m)))
    (hP : (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + m)))
    (hQ : (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + m))) :
    let K := Real.log 2 + 6 * rangedPairExponent n b d C S H
    2 * ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (f.budget T t ht * f'.budget T' t' ht') ^ 2 ≤
      Real.exp (K * (1 + m) ^ (n + 2)) ∧
    2 * ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B : ℕ) *
        (3 ^ (2 * (((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)) +
          ((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)))) : ℕ) *
        (f.budget T t ht * f'.budget T' t' ht') ^ 2 ≤
      Real.exp (K * (1 + m) ^ (n + 2)) := by
  let W := wordPeriodExponent n b
  let R := (((3 * 2 ^ n + 3 * (2 ^ n - 1) : ℕ) : ℝ) + 4 * d) * b ^ (n + 1)
  let F := (4 * S + 2 * C) * (2 ^ n : ℕ)
  let K₀ := rangedPairExponent n b d C S H
  have hW : 0 ≤ W := by dsimp [W, wordPeriodExponent]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hK₀ : 0 ≤ K₀ := rangedPairExponent_nonneg n b d C S H hb hd hC (by linarith) hH
  have hpow : 1 + m ≤ (1 + m) ^ (n + 2) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ 1 + m)
      (show 1 ≤ n + 2 by omega)
  have hunit : 1 ≤ (1 + m) ^ (n + 2) := one_le_pow₀ (by linarith)
  have hKeq : K₀ = H + 2 * C * W + 4 * Real.log 3 * R + 2 * F := by
    dsimp [K₀, rangedPairExponent, W, R, F]
    ring
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hCW : 0 ≤ 2 * C * W := by positivity
  have hRR : 0 ≤ 4 * Real.log 3 * R := by positivity
  have hHK : H ≤ K₀ := by rw [hKeq]; linarith
  have hWK : 2 * C * W ≤ K₀ := by rw [hKeq]; linarith
  have hRK : 4 * Real.log 3 * R ≤ K₀ := by rw [hKeq]; linarith
  have hFK : 2 * F ≤ K₀ := by rw [hKeq]; linarith
  have hlift (a : ℝ) (ha : 0 ≤ a) (haK : a ≤ K₀) :
      a * (1 + m) ≤ K₀ * (1 + m) ^ (n + 2) :=
    (mul_le_mul_of_nonneg_left hpow ha).trans
      (mul_le_mul_of_nonneg_right haK (by positivity))
  have hfreq (s : ℤ) (hs : s.natAbs ≤ V) : |(s : ℝ)| ≤ Real.exp (C * (1 + m)) := by
    have hh : |(s : ℝ)| ≤ (V : ℝ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using (show (s.natAbs : ℝ) ≤ (V : ℝ) from by exact_mod_cast hs)
    exact hh.trans hV
  have hbudget := f.budget_le_exp T t ht S C m hS hC hm hs₀ hs₁
    (fun s hs => hfreq s (hf s hs)) hr
  have hbudget' := f'.budget_le_exp T' t' ht' S C m hS hC hm hs₀' hs₁'
    (fun s hs => hfreq s (hf' s hs)) hr'
  have hBpair : f.budget T t ht * f'.budget T' t' ht' ≤
      Real.exp (K₀ * (1 + m) ^ (n + 2)) := by
    calc
      _ ≤ Real.exp (F * (1 + m)) * Real.exp (F * (1 + m)) :=
        mul_le_mul hbudget hbudget' (f'.budget_nonneg _ _ _) (Real.exp_nonneg _)
      _ = Real.exp ((2 * F) * (1 + m)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (hlift (2 * F) (by positivity) hFK)
  have hperiod : (wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B : ℝ) ≤
      Real.exp (K₀ * (1 + m) ^ (n + 2)) := by
    calc
      _ ≤ Real.exp (C * W * (1 + m) ^ (n + 2)) *
          Real.exp (C * W * (1 + m) ^ (n + 2)) :=
        mul_le_mul (wordTransferFullPeriod_le_exp n t B V b C m hC hm hB hV hf)
          (wordTransferFullPeriod_le_exp n t' B V b C m hC hm hB hV hf')
          (by positivity) (Real.exp_nonneg _)
      _ = Real.exp ((2 * C * W) * (1 + m) ^ (n + 2)) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hWK (by positivity))
  have hpartition := ranged_boolean_partition_le D D' B R m
    (ranged_word_complexity_le D D' B b d m hd hm hB hD hD')
  have hpartition' := hpartition.trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hRK (by positivity : 0 ≤ (1 + m) ^ (n + 2))))
  have hcost := dyadic_character_cost ((Nat.log 2 E + 1 : ℕ) : ℝ)
    (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹
    (wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B : ℕ)
    (3 ^ (2 * (((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)) +
      ((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)))) : ℕ)
    (f.budget T t ht * f'.budget T' t' ht') (K₀ * (1 + m) ^ (n + 2))
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (mul_nonneg (f.budget_nonneg _ _ _) (f'.budget_nonneg _ _ _)) (by positivity)
    (hE.trans (Real.exp_le_exp.mpr (hlift H hH hHK)))
    (hP.trans (Real.exp_le_exp.mpr (hlift H hH hHK)))
    (hQ.trans (Real.exp_le_exp.mpr (hlift H hH hHK)))
    (by exact_mod_cast hperiod) hpartition' hBpair
  have hexp : Real.log 2 + 6 * (K₀ * (1 + m) ^ (n + 2)) ≤
      (Real.log 2 + 6 * K₀) * (1 + m) ^ (n + 2) := by
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  exact ⟨hcost.1.trans (Real.exp_le_exp.mpr hexp), hcost.2.trans (Real.exp_le_exp.mpr hexp)⟩

/-- The dyadic shell count uses only a double-exponential endpoint bound;
its own cost is singly exponential in the word length. -/
theorem dyadic_shell_linear_exponential (E : ℕ) (C m : ℝ)
    (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hE : (E : ℝ) ≤ Real.exp (Real.exp (C * (1 + m)))) :
    ((Nat.log 2 E + 1 : ℕ) : ℝ) ≤
      Real.exp ((2 + 1 / Real.log 2 + C) * (1 + m)) := by
  let a : ℝ := 2 + 1 / Real.log 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hT : 1 ≤ Real.exp (C * (1 + m)) := Real.one_le_exp (by positivity)
  have hc := dyadic_shell_count_bound 1 (Real.exp (C * (1 + m)))
    (by norm_num) hT E (by simpa only [one_mul] using hE)
  have hea : a ≤ Real.exp a := by linarith [Real.add_one_le_exp a]
  push_cast
  calc
    _ ≤ a * Real.exp (C * (1 + m)) := hc
    _ ≤ Real.exp a * Real.exp (C * (1 + m)) :=
      mul_le_mul_of_nonneg_right hea (Real.exp_nonneg _)
    _ = Real.exp (a + C * (1 + m)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [a] at *; nlinarith)

end Ostmann

end OAI
