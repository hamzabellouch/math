import OAI.Computability.PerfectCompleteness.Construction.HiddenChildMixture
import OAI.Computability.PerfectCompleteness.Foundations.FiniteProduct
import OAI.Computability.PerfectCompleteness.Repetition.RepetitionRateLemmas
import OAI.Computability.PerfectCompleteness.Sampling.DensityVariation
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas

namespace OAI


namespace PerfectCompleteness.CoordinateReplacement

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def ratio (P Q : (i : I) → FiniteDistribution (Ω i)) (i : I) (a : Ω i) : ℝ :=
  (Q i).weight a / (P i).weight a

def replacement (P Q : (i : I) → FiniteDistribution (Ω i)) (i : I) :
    FiniteDistribution ((j : I) → Ω j) :=
  law (Function.update P i (Q i))

omit [Fintype I] [DecidableEq I] in
theorem ratio_nonnegative (P Q : (i : I) → FiniteDistribution (Ω i))
    (i : I) (a : Ω i) : 0 ≤ ratio P Q i a :=
  div_nonneg ((Q i).nonnegative a) ((P i).nonnegative a)

omit [Fintype I] [DecidableEq I] in
theorem support_of_positive (P Q : (i : I) → FiniteDistribution (Ω i))
    (positive : ∀ i a, 0 < (P i).weight a) :
    ∀ i a, (P i).weight a = 0 → (Q i).weight a = 0 := by
  intro i a hzero
  exact False.elim ((ne_of_gt (positive i a)) hzero)

omit [Fintype I] [DecidableEq I] in

theorem support_of_domination (P Q : (i : I) → FiniteDistribution (Ω i))
    (B : ℝ) (domination : ∀ i a, (Q i).weight a ≤ B * (P i).weight a) :
    ∀ i a, (P i).weight a = 0 → (Q i).weight a = 0 := by
  intro i a hzero
  apply le_antisymm
  · simpa only [hzero, mul_zero] using domination i a
  · exact (Q i).nonnegative a

omit [Fintype I] [DecidableEq I] in
theorem weight_mul_ratio_of_support (P Q : (i : I) → FiniteDistribution (Ω i))
    (support : ∀ i a, (P i).weight a = 0 → (Q i).weight a = 0)
    (i : I) (a : Ω i) :
    (P i).weight a * ratio P Q i a = (Q i).weight a := by
  by_cases hzero : (P i).weight a = 0
  · simp only [hzero, zero_mul, support i a hzero]
  · exact mul_div_cancel₀ ((Q i).weight a) hzero

omit [Fintype I] [DecidableEq I] in
theorem ratio_mean_one_of_support (P Q : (i : I) → FiniteDistribution (Ω i))
    (support : ∀ i a, (P i).weight a = 0 → (Q i).weight a = 0) (i : I) :
    (P i).expectation (ratio P Q i) = 1 := by
  change (∑ a, (P i).weight a * ratio P Q i a) = 1
  simp_rw [weight_mul_ratio_of_support P Q support]
  exact (Q i).normalized

omit [Fintype I] [DecidableEq I] in
theorem ratio_mean_one (P Q : (i : I) → FiniteDistribution (Ω i))
    (positive : ∀ i a, 0 < (P i).weight a) (i : I) :
    (P i).expectation (ratio P Q i) = 1 :=
  ratio_mean_one_of_support P Q (support_of_positive P Q positive) i

omit [Fintype I] [DecidableEq I] in
theorem ratio_mean_one_of_domination (P Q : (i : I) → FiniteDistribution (Ω i))
    (B : ℝ) (domination : ∀ i a, (Q i).weight a ≤ B * (P i).weight a) (i : I) :
    (P i).expectation (ratio P Q i) = 1 :=
  ratio_mean_one_of_support P Q (support_of_domination P Q B domination) i

theorem replacement_weight_of_support (P Q : (i : I) → FiniteDistribution (Ω i))
    (support : ∀ i a, (P i).weight a = 0 → (Q i).weight a = 0)
    (i : I) (x : (j : I) → Ω j) :
    (replacement P Q i).weight x = (law P).weight x * ratio P Q i (x i) := by
  have hrow (j : I) :
      (Function.update P i (Q i) j).weight (x j) =
        (P j).weight (x j) * factor i (ratio P Q i) j (x j) := by
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self, factor_self]
      exact (weight_mul_ratio_of_support P Q support i (x i)).symm
    · simp only [Function.update_of_ne hji, factor_other i j hji, mul_one]
  change (∏ j, (Function.update P i (Q i) j).weight (x j)) =
    (∏ j, (P j).weight (x j)) * ratio P Q i (x i)
  simp_rw [hrow]
  rw [Finset.prod_mul_distrib, product_factor]

theorem replacement_weight (P Q : (i : I) → FiniteDistribution (Ω i))
    (positive : ∀ i a, 0 < (P i).weight a) (i : I) (x : (j : I) → Ω j) :
    (replacement P Q i).weight x = (law P).weight x * ratio P Q i (x i) :=
  replacement_weight_of_support P Q (support_of_positive P Q positive) i x

theorem replacement_weight_of_domination (P Q : (i : I) → FiniteDistribution (Ω i))
    (B : ℝ) (domination : ∀ i a, (Q i).weight a ≤ B * (P i).weight a)
    (i : I) (x : (j : I) → Ω j) :
    (replacement P Q i).weight x = (law P).weight x * ratio P Q i (x i) :=
  replacement_weight_of_support P Q (support_of_domination P Q B domination) i x

omit [Fintype I] [DecidableEq I] in
theorem ratio_le_of_positive (P Q : (i : I) → FiniteDistribution (Ω i))
    (positive : ∀ i a, 0 < (P i).weight a) (B : ℝ)
    (domination : ∀ i a, (Q i).weight a ≤ B * (P i).weight a)
    (i : I) (a : Ω i) : ratio P Q i a ≤ B :=
  (div_le_iff₀ (positive i a)).2 (domination i a)

omit [Fintype I] [DecidableEq I] in
theorem ratio_bounds_of_domination (P Q : (i : I) → FiniteDistribution (Ω i))
    (B : ℝ) (nonnegative : 0 ≤ B)
    (domination : ∀ i a, (Q i).weight a ≤ B * (P i).weight a)
    (i : I) (a : Ω i) : 0 ≤ ratio P Q i a ∧ ratio P Q i a ≤ B := by
  refine ⟨ratio_nonnegative P Q i a, ?_⟩
  by_cases hzero : (P i).weight a = 0
  · simpa only [ratio, hzero, div_zero] using nonnegative
  · exact (div_le_iff₀ (lt_of_le_of_ne ((P i).nonnegative a) (Ne.symm hzero))).2
      (domination i a)

omit [Fintype I] [DecidableEq I] in

theorem ratio_second_moment_le (P Q : (i : I) → FiniteDistribution (Ω i))
    (B : ℝ) (nonnegative : 0 ≤ B)
    (domination : ∀ i a, (Q i).weight a ≤ B * (P i).weight a) (i : I) :
    (P i).expectation (fun a => (ratio P Q i a - 1) ^ 2) ≤ B - 1 := by
  have hpoint (a : Ω i) :
      (ratio P Q i a - 1) ^ 2 ≤ (B - 2) * ratio P Q i a + 1 := by
    obtain ⟨hpos, hbound⟩ := ratio_bounds_of_domination P Q B nonnegative domination i a
    have hmul := mul_le_mul_of_nonneg_right hbound hpos
    nlinarith
  have hexpectation :
      (P i).expectation (fun a => (B - 2) * ratio P Q i a + 1) =
        (B - 2) * (P i).expectation (ratio P Q i) + 1 := by
    unfold FiniteDistribution.expectation
    rw [Finset.mul_sum]
    simp only [mul_add, mul_one, Finset.sum_add_distrib]
    rw [(P i).normalized]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    ring
  calc
    _ ≤ (P i).expectation (fun a => (B - 2) * ratio P Q i a + 1) :=
      SmallBias.expectation_mono (P i) hpoint
    _ = (B - 2) * (P i).expectation (ratio P Q i) + 1 := hexpectation
    _ = B - 1 := by
      rw [ratio_mean_one_of_domination P Q B domination i]
      ring

theorem observed_replacement_variation [Nonempty I] {Γ : Type*} [Fintype Γ]
    (P Q : (i : I) → FiniteDistribution (Ω i)) (B : ℝ) (nonnegative : 0 ≤ B)
    (domination : ∀ i a, (Q i).weight a ≤ B * (P i).weight a)
    (observe : ((i : I) → Ω i) → Γ) :
    ((HiddenChildMixture.mixture (replacement P Q)).pushforward observe).totalVariation
        ((law P).pushforward observe) ≤
      Real.sqrt ((B - 1) / Fintype.card I) / 2 :=
  HiddenChildMixture.observed_mixture_variation P (replacement P Q) (ratio P Q)
    (replacement_weight_of_domination P Q B domination)
    (ratio_mean_one_of_domination P Q B domination)
    (B - 1) (ratio_second_moment_le P Q B nonnegative domination) observe


variable [∀ i, Nonempty (Ω i)]

omit [Fintype I] [DecidableEq I] in

theorem uniform_domination (Q : (i : I) → FiniteDistribution (Ω i)) (B : ℝ)
    (cardinality : ∀ i, (Fintype.card (Ω i) : ℝ) ≤ B) (i : I) (a : Ω i) :
    (Q i).weight a ≤ B * (FiniteDistribution.uniform (Ω i)).weight a := by
  classical
  have hweight : (Q i).weight a ≤ 1 := by
    calc
      _ ≤ ∑ b, (Q i).weight b :=
        Finset.single_le_sum (fun b _ => (Q i).nonnegative b) (Finset.mem_univ a)
      _ = 1 := (Q i).normalized
  have hcard : 0 < (Fintype.card (Ω i) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  change (Q i).weight a ≤ B * (1 / (Fintype.card (Ω i) : ℝ))
  calc
    _ ≤ 1 := hweight
    _ ≤ B * (1 / (Fintype.card (Ω i) : ℝ)) := by
      rw [mul_one_div]
      exact (one_le_div hcard).2 (cardinality i)

theorem observed_uniform_replacement_variation [Nonempty I]
    {Γ : Type*} [Fintype Γ]
    (Q : (i : I) → FiniteDistribution (Ω i)) (B : ℝ)
    (cardinality : ∀ i, (Fintype.card (Ω i) : ℝ) ≤ B)
    (observe : ((i : I) → Ω i) → Γ) :
    ((HiddenChildMixture.mixture
        (replacement (fun i => FiniteDistribution.uniform (Ω i)) Q)).pushforward observe).totalVariation
        ((law (fun i => FiniteDistribution.uniform (Ω i))).pushforward observe) ≤
      Real.sqrt ((B - 1) / Fintype.card I) / 2 := by
  have hB : 0 ≤ B := by
    obtain ⟨i⟩ := ‹Nonempty I›
    exact (Nat.cast_nonneg (Fintype.card (Ω i))).trans (cardinality i)
  exact observed_replacement_variation (fun i => FiniteDistribution.uniform (Ω i)) Q B hB
    (uniform_domination Q B cardinality) observe


end
end PerfectCompleteness.CoordinateReplacement



namespace PerfectCompleteness.CubicErrorBounds

theorem pow_sub_one_le_twice {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1)
    (n : Nat) (hsmall : (n : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ n - 1 ≤ 2 * ((n : ℝ) * x) := by
  have hbern := one_add_mul_le_pow (a := -x) (by linarith : (-2 : ℝ) ≤ -x) n
  have hprod : (1 + x) ^ n * (1 - x) ^ n ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀ (by nlinarith) (by nlinarith)
  have hA : 0 ≤ (1 + x) ^ n := pow_nonneg (by linarith) _
  have hmul := mul_le_mul_of_nonneg_left hbern hA
  simp only [← sub_eq_add_neg, mul_neg] at hmul
  have hbound : (1 + x) ^ n * (1 - (n : ℝ) * x) ≤ 1 := by
    nlinarith
  have hA2 : (1 + x) ^ n ≤ 2 := by nlinarith
  have hnx : 0 ≤ (n : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx
  nlinarith

theorem cube_exponent_identity {m : Nat} (hm : 0 < m) (L : ℝ) :
    ((m ^ 3 : Nat) : ℝ) * (L ^ 2 / (m : ℝ) ^ 4) = L ^ 2 / m := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  push_cast
  field_simp

theorem sparse_cube_bound {m : Nat} (hm : 0 < m) (L : ℝ)
    (hsmall : L ^ 2 / (m : ℝ) ≤ 1 / 2) :
    (1 + L ^ 2 / (m : ℝ) ^ 4) ^ (m ^ 3) - 1 ≤ 2 * L ^ 2 / m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hpow : (m : ℝ) ≤ (m : ℝ) ^ 4 := by nlinarith [sq_nonneg ((m : ℝ) ^ 2 - 1)]
  have hx : L ^ 2 / (m : ℝ) ^ 4 ≤ 1 := by
    have h := div_le_div_of_nonneg_left (sq_nonneg L) hmpos hpow
    linarith
  have h := pow_sub_one_le_twice (by positivity) hx (m ^ 3)
    (by simpa only [cube_exponent_identity hm] using hsmall)
  simpa only [cube_exponent_identity hm, mul_div_assoc] using h

theorem posterior_cube_bound {m : Nat} (hm : 2 ≤ m) {L : ℝ} (hL : 0 ≤ L) :
    2 * ((1 / (m : ℝ) ^ 2) * L / (1 - 1 / (m : ℝ) ^ 2)) ≤ 4 * L / (m : ℝ) ^ 2 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hsq : (4 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hsqpos : (0 : ℝ) < (m : ℝ) ^ 2 := by linarith
  have hfrac : (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ hsqpos).2
    linarith
  have hden : (0 : ℝ) < 1 - 1 / (m : ℝ) ^ 2 := by linarith
  apply (le_div_iff₀ hsqpos).2
  rw [mul_assoc, div_mul_eq_mul_div, ← mul_div_assoc]
  apply (div_le_iff₀ hden).2
  have heq : 2 * ((1 / (m : ℝ) ^ 2) * L * (m : ℝ) ^ 2) = 2 * L := by
    field_simp
  nlinarith [mul_nonneg hL (sub_nonneg.mpr hfrac)]

end PerfectCompleteness.CubicErrorBounds



namespace PerfectCompleteness.CubicErrorSchedule

open CubicErrorBounds

theorem power_mul_growth_le_one {b : ℝ} (hb : 0 ≤ b) (_ : b ≤ 1)
    (n : Nat) : b ^ n * (1 + (n : ℝ) * (1 - b)) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hstep : b * (1 + ((n : ℝ) + 1) * (1 - b)) ≤
        1 + (n : ℝ) * (1 - b) := by nlinarith [mul_nonneg hn (sq_nonneg (1-b))]
    have hprod := mul_le_mul_of_nonneg_left hstep (pow_nonneg hb n)
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem clean_cube_bound {c : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1)
    {m : Nat} (hm : 0 < m) :
    (1 - c / (m : ℝ) ^ 2) ^ (m ^ 3) ≤ 1 / (1 + c * m) := by
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsq : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hfrac : c / (m : ℝ) ^ 2 ≤ 1 := (div_le_one (by positivity)).2 (hc'.trans hsq)
  have h := power_mul_growth_le_one (by linarith : 0 ≤ 1-c/(m:ℝ)^2)
    (by have := div_nonneg hc (sq_nonneg (m:ℝ)); linarith : 1-c/(m:ℝ)^2 ≤ 1) (m^3)
  have heq : 1 + ((m ^ 3 : Nat) : ℝ) * (1-(1-c/(m:ℝ)^2)) = 1+c*m := by
    push_cast
    field_simp
    ring
  rw [heq] at h
  exact (le_div_iff₀ (by positivity)).2 h

theorem exists_cube_errors_lt {L c ε : ℝ} (hL : 0 ≤ L)
    (hc : 0 < c) (hc' : c ≤ 1) (hε : 0 < ε) :
    ∃ m : Nat, 2 ≤ m ∧
      Real.sqrt (L ^ 2 / (m : ℝ) ^ 3) / 2 < ε ∧
      Real.sqrt ((1 + L ^ 2 / (m : ℝ) ^ 4) ^ (m ^ 3) - 1) / 2 < ε ∧
      2 * ((1 / (m : ℝ) ^ 2) * L / (1 - 1 / (m : ℝ) ^ 2)) < ε ∧
      (1 - c / (m : ℝ) ^ 2) ^ (m ^ 3) < ε := by
  obtain ⟨m, hm⟩ := exists_nat_gt
    (2 + 2 * L ^ 2 + 2 * L ^ 2 / ε ^ 2 + 4 * L / ε + 1 / (c * ε))
  have hs : 0 ≤ 2 * L ^ 2 / ε ^ 2 := by positivity
  have hp : 0 ≤ 4 * L / ε := by positivity
  have hd : 0 ≤ 1 / (c * ε) := by positivity
  have hm2r : (2 : ℝ) < m := by nlinarith [sq_nonneg L]
  have hm2 : 2 ≤ m := by exact_mod_cast hm2r.le
  have hm0 : 0 < m := by omega
  have hmr : (0 : ℝ) < m := by positivity
  have hsmall : L ^ 2 / (m : ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hmr).2
    nlinarith
  have hlarge : 2 * L ^ 2 / ε ^ 2 < (m : ℝ) := by nlinarith [sq_nonneg L]
  have hvar : 2 * L ^ 2 / (m : ℝ) < ε ^ 2 := by
    apply (div_lt_iff₀ hmr).2
    have h := (div_lt_iff₀ (sq_pos_of_pos hε)).1 hlarge
    nlinarith
  have hm3 : (m : ℝ) ≤ (m : ℝ)^3 := by nlinarith [sq_nonneg ((m : ℝ)-1)]
  have hidden : L ^ 2 / (m : ℝ)^3 < ε ^ 2 := by
    have h := div_le_div_of_nonneg_left (sq_nonneg L) hmr hm3
    have hn : 0 ≤ L^2/(m:ℝ) := by positivity
    rw [mul_div_assoc] at hvar
    linarith
  have sparse : (1+L^2/(m:ℝ)^4)^(m^3)-1 < ε^2 :=
    (sparse_cube_bound hm0 L hsmall).trans_lt hvar
  have hsqrt {x : ℝ} (hx : x < ε^2) : Real.sqrt x / 2 < ε := by
    have h := (Real.sqrt_lt' hε).2 hx
    linarith
  refine ⟨m, hm2, hsqrt hidden, hsqrt sparse, ?_, ?_⟩
  · apply (posterior_cube_bound hm2 hL).trans_lt
    have hlarge : 4*L/ε < (m:ℝ) := by nlinarith [sq_nonneg L]
    have hsq : (m:ℝ) ≤ (m:ℝ)^2 := by nlinarith
    apply (div_le_div_of_nonneg_left (by positivity : 0≤4*L) hmr hsq).trans_lt
    apply (div_lt_iff₀ hmr).2
    have h := (div_lt_iff₀ hε).1 hlarge
    nlinarith
  · apply (clean_cube_bound hc.le hc' hm0).trans_lt
    have hlarge : 1/(c*ε) < (m:ℝ) := by nlinarith [sq_nonneg L]
    have h := (div_lt_iff₀ (mul_pos hc hε)).1 hlarge
    apply (div_lt_iff₀ (by positivity : 0 < 1+c*m)).2
    nlinarith

end PerfectCompleteness.CubicErrorSchedule

end OAI
