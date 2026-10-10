import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Epsilon
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ChargeKappaPos
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneBounded
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Core
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CorePrime
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeWeight
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.PrimeDefect

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology
open MeasureTheory intervalIntegral
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Filter Finset

namespace OrdinaryCorrelations.RawDivisorBin
open OrdinaryAnalyticCentering ElliottReductions

lemma one_add_sum_le_product {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    1 + ∑ i ∈ S, w i ≤ ∏ i ∈ S, (1 + w i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have has := hw a (mem_insert_self _ _)
    have hss : ∀ i ∈ S, 0 ≤ w i := fun i hi => hw i (mem_insert_of_mem hi)
    have hs := sum_nonneg hss
    have hp := ih hss
    rw [sum_insert ha, prod_insert ha]
    nlinarith [mul_nonneg has hs, mul_le_mul_of_nonneg_left hp has]

lemma one_sub_product_le_sum {ι : Type*} (S : Finset ι) (r : ι → ℝ)
    (hr0 : ∀ i ∈ S, 0 ≤ r i) (hr1 : ∀ i ∈ S, r i ≤ 1) :
    1 - ∏ i ∈ S, r i ≤ ∑ i ∈ S, (1 - r i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hr0' := fun i hi => hr0 i (mem_insert_of_mem hi)
    have hr1' := fun i hi => hr1 i (mem_insert_of_mem hi)
    have hp : 0 ≤ ∏ i ∈ S, r i := prod_nonneg hr0'
    have hp1 : (∏ i ∈ S, r i) ≤ 1 := prod_le_one₀ hr0' hr1'
    have ih' := ih hr0' hr1'
    rw [prod_insert ha, sum_insert ha]
    nlinarith [mul_nonneg (sub_nonneg.mpr (hr1 a (mem_insert_self _ _)))
      (sub_nonneg.mpr hp1)]

lemma core_eq_source (B : ℝ) : core B = SourcePrimeBands.corePrimes B := by
  ext p
  simp only [core, SourcePrimeBands.corePrimes, mem_filter]
  constructor
  · rintro ⟨hp, hpr, hl, hu⟩
    refine ⟨hp, hpr, ?_⟩
    simpa only [SourcePrimeBands.eta, SourcePrimeBands.epsilon, show (1 - 1 / 10000 / 100 : ℝ) = 999999 / 1000000 by norm_num] using hl
  · rintro ⟨hp, hpr, hl⟩
    refine ⟨hp, hpr, ?_, ?_⟩
    · simpa only [SourcePrimeBands.eta, SourcePrimeBands.epsilon, show (1 - 1 / 10000 / 100 : ℝ) = 999999 / 1000000 by norm_num] using hl
    · have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
      apply (Real.log_le_iff_le_exp hp0).mpr
      exact (Nat.le_floor_iff (Real.exp_pos B).le).mp (mem_Icc.mp hp).2

lemma primeWeight_le (B : ℝ) (p : ℕ) : primeWeight B p ≤ A / p := by
  have hA : 1 ≤ A := Real.one_le_exp (by norm_num)
  unfold primeWeight
  split_ifs
  · rfl
  · simpa only [one_div] using div_le_div_of_nonneg_right hA (Nat.cast_nonneg p)

lemma source_prime_subset (B : ℝ) :
    core B ∪ center B ⊆ (Finset.Icc 2 ⌊Real.exp B⌋₊).filter Nat.Prime := by
  intro p hp
  rcases mem_union.mp hp with hp | hp <;>
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1, (mem_filter.mp hp).2.1⟩

lemma L₀_ge_one (B : ℝ) : 1 ≤ L₀ B := by
  rw [← euler_product]
  have h := single_le_sum (f := fun R : Finset ℕ => ∏ p ∈ R, primeWeight B p) (fun R hR => prod_nonneg (fun p hp => primeWeight_nonneg B p))
    (show ∅ ∈ (core B ∪ center B).powerset by simp)
  simpa only [Finset.prod_empty] using h

lemma L₀_tendsto : Tendsto L₀ atTop atTop := by
  apply tendsto_atTop_mono (f := SourcePrimeBands.coreMass)
  · intro B
    have hA : 1 ≤ A := Real.one_le_exp (by norm_num)
    have h : ∑ p ∈ core B, (p : ℝ)⁻¹ ≤ ∑ p ∈ core B, primeWeight B p := by
      apply sum_le_sum
      intro p hp
      simp only [primeWeight, ite_eq_left hp]
      simpa only [one_div] using div_le_div_of_nonneg_right hA (Nat.cast_nonneg p)
    have hs : ∑ p ∈ core B, primeWeight B p ≤ ∑ p ∈ core B ∪ center B, primeWeight B p :=
      sum_le_sum_of_subset_of_nonneg subset_union_left (fun p hp hn => primeWeight_nonneg B p)
    have hprod : ∑ p ∈ core B ∪ center B, primeWeight B p ≤
        ∏ p ∈ core B ∪ center B, (1 + primeWeight B p) := by
      have := one_add_sum_le_product (core B ∪ center B) (primeWeight B) (fun p hp => primeWeight_nonneg B p)
      linarith
    rw [prod_one_add, euler_product] at hprod
    simpa only [SourcePrimeBands.coreMass, core_eq_source] using h.trans (hs.trans hprod)
  · exact GraphKernel.PrimeSystem.coreMass_tendsto

lemma subset_multiplicative (f : ℕ → ℂ) (hm : Multiplicative f) (h1 : f 1 = 1)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    f (∏ p ∈ S, p) = ∏ p ∈ S, f p := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using h1
  | @insert p S hp ih =>
    have hSp : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    have hpp := hS p (mem_insert_self _ _)
    have hcop : p.Coprime (∏ q ∈ S, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (hpp.coprime_iff_not_dvd).mpr (by
        intro hpq
        have he := (Nat.prime_dvd_prime_iff_eq hpp (hSp q hq)).mp hpq
        exact hp (he.symm ▸ hq))
    rw [prod_insert hp, prod_insert hp, hm _ _ hpp.pos (prod_pos (fun q hq => (hSp q hq).pos)) hcop,
      ih hSp]

lemma product_modulus_defect (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (hmf : Multiplicative f) (hmg : Multiplicative g) (h1f : f 1 = 1) (h1g : g 1 = 1)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    1 - ‖f (∏ p ∈ S, p) * g (∏ p ∈ S, p)‖ ≤ ∑ p ∈ S, (1 - ‖f p * g p‖) := by
  rw [subset_multiplicative f hmf h1f S hS, subset_multiplicative g hmg h1g S hS,
    ← prod_mul_distrib, norm_prod]
  exact one_sub_product_le_sum S (fun p => ‖f p * g p‖) (fun p hp => norm_nonneg _) (fun p hp => by
    rw [norm_mul]
    exact (mul_le_mul (hf p) (hg p) (norm_nonneg _) zero_le_one).trans (by norm_num))

lemma modulus_product_le_one (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g) (n : ℕ) :
    ‖f n * g n‖ ≤ 1 := by
  rw [norm_mul]
  exact (mul_le_mul (hf n) (hg n) (norm_nonneg _) zero_le_one).trans (by norm_num)

lemma modulus_defect_le (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g) (p : ℕ) :
    1 - ‖f p * g p‖ ≤ (1 - ‖f p‖) + (1 - ‖g p‖) := by
  rw [norm_mul]
  nlinarith [mul_nonneg (sub_nonneg.mpr (hf p)) (sub_nonneg.mpr (hg p))]

lemma first_moments_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℝ in atTop,
    (∑ p ∈ core B ∪ center B, primeWeight B p / (1 + primeWeight B p)) ≤ K * Real.log B ∧
    (∑ p ∈ core B ∪ center B, primeWeight B p * Real.log p / (1 + primeWeight B p)) ≤ K * B := by
  have hA : 0 < A := Real.exp_pos _
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨2*A*(1+Real.log 4), by positivity, ?_⟩
  have ht : Tendsto (fun B : ℝ => SourcePrimeBands.primeHarmonic (Real.exp B) / Real.log B)
      atTop (nhds 1) := by
    simpa only [Real.rpow_one] using
      SourcePrimeBands.primeHarmonic_exp_rpow_ratio (by norm_num : (0:ℝ) < 1)
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (1:ℝ) < 2)),
    eventually_ge_atTop (2:ℝ), Real.tendsto_exp_atTop.eventually_ge_atTop 2] with B hrat hB hE
  have hl : 0 < Real.log B := Real.log_pos (by linarith)
  have hm : SourcePrimeBands.primeHarmonic (Real.exp B) ≤ 2*Real.log B :=
    ((div_lt_iff₀ hl).mp hrat).le
  constructor
  · calc
      _ ≤ ∑ p ∈ core B ∪ center B, primeWeight B p := by
        apply sum_le_sum
        intro p hp
        exact div_le_self (primeWeight_nonneg B p) (by linarith [primeWeight_nonneg B p])
      _ ≤ ∑ p ∈ core B ∪ center B, A / p := sum_le_sum (fun p hp => primeWeight_le B p)
      _ ≤ ∑ p ∈ (Finset.Icc 2 ⌊Real.exp B⌋₊).filter Nat.Prime, A / p :=
        sum_le_sum_of_subset_of_nonneg (source_prime_subset B) (fun p hp hn => by positivity)
      _ = A * SourcePrimeBands.primeHarmonic (Real.exp B) := by simp [SourcePrimeBands.primeHarmonic, mul_sum, div_eq_mul_inv]
      _ ≤ A * (2 * Real.log B) := mul_le_mul_of_nonneg_left hm hA.le
      _ ≤ (2*A*(1+Real.log 4))*Real.log B := by nlinarith [mul_nonneg (mul_nonneg hA.le hlog4) hl.le]
  · have hprime := SourcePrimeBands.logPrimeReciprocal_le hE
    rw [Real.log_exp] at hprime
    calc
      _ ≤ ∑ p ∈ core B ∪ center B, primeWeight B p * Real.log p := by
        apply sum_le_sum
        intro p hp
        exact div_le_self (mul_nonneg (primeWeight_nonneg B p) (Real.log_natCast_nonneg p))
          (by linarith [primeWeight_nonneg B p])
      _ ≤ ∑ p ∈ core B ∪ center B, A * (Real.log p / p) := by
        apply sum_le_sum
        intro p hp
        have := mul_le_mul_of_nonneg_right (primeWeight_le B p) (Real.log_natCast_nonneg p)
        simpa only [div_mul_eq_mul_div, mul_div_assoc] using this
      _ ≤ ∑ p ∈ (Finset.Icc 2 ⌊Real.exp B⌋₊).filter Nat.Prime, A * (Real.log p / p) :=
        sum_le_sum_of_subset_of_nonneg (source_prime_subset B)
          (fun p hp hn => mul_nonneg hA.le (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)))
      _ = A * (∑ p ∈ (Finset.Icc 2 ⌊Real.exp B⌋₊).filter Nat.Prime, Real.log p / p) := (mul_sum ..).symm
      _ ≤ A * (Real.log 4 * (1 + B)) := mul_le_mul_of_nonneg_left hprime hA.le
      _ ≤ (2*A*(1+Real.log 4))*B := by
        have hAB := mul_nonneg hA.le (show 0 ≤ B by linarith)
        have hprod := mul_nonneg (mul_nonneg hA.le hlog4) (show 0 ≤ B-1 by linarith)
        nlinarith

lemma defect_first_moment_small (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (hfd : Summable (primeDefect f)) (hgd : Summable (primeDefect g))
    (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ B : ℝ in atTop,
    (∑ p ∈ core B ∪ center B,
      primeWeight B p * (1 - ‖f p * g p‖) / (1 + primeWeight B p)) ≤ δ := by
  have hA : 0 < A := Real.exp_pos _
  obtain ⟨S, hS⟩ := summable_iff_vanishing_norm.mp (hfd.add hgd) (δ/A) (div_pos hδ hA)
  have ht : Tendsto P₀ atTop atTop := Real.tendsto_exp_atTop.comp
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 9999/10000))
  filter_upwards [ht.eventually_ge_atTop ((S.sup id : ℕ) : ℝ), eventually_ge_atTop (1:ℝ)] with B hB hB1
  have hdisj : Disjoint (core B ∪ center B) S := by
    apply Finset.disjoint_left.mpr
    intro p hp hps
    have hps' : (p : ℝ) ≤ ((S.sup id : ℕ) : ℝ) := by exact_mod_cast (le_sup (f := id) hps)
    exact (not_lt_of_ge (hps'.trans hB)) (prime_lower B hB1 hp)
  have hb := hS (core B ∪ center B) hdisj
  rw [Real.norm_eq_abs, abs_of_nonneg (sum_nonneg (fun p hp =>
    add_nonneg (primeDefect_nonneg hf p) (primeDefect_nonneg hg p)))] at hb
  have hsum : (∑ p ∈ core B ∪ center B,
      primeWeight B p * (1 - ‖f p * g p‖) / (1 + primeWeight B p)) ≤
      A * ∑ p ∈ core B ∪ center B, (primeDefect f p + primeDefect g p) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hp' := (mem_filter.mp (source_prime_subset B hp)).2
    calc
      _ ≤ primeWeight B p * (1 - ‖f p * g p‖) :=
        div_le_self (mul_nonneg (primeWeight_nonneg B p)
          (sub_nonneg.mpr (modulus_product_le_one f g hf hg p))) (by linarith [primeWeight_nonneg B p])
      _ ≤ (A/p) * ((1 - ‖f p‖) + (1 - ‖g p‖)) :=
        mul_le_mul (primeWeight_le B p) (modulus_defect_le f g hf hg p)
          (sub_nonneg.mpr (modulus_product_le_one f g hf hg p)) (by positivity)
      _ = A * (primeDefect f p + primeDefect g p) := by
        simp only [primeDefect, ite_eq_left hp']
        ring
  exact hsum.trans (by have := (lt_div_iff₀ hA).mp hb; nlinarith)

end OrdinaryCorrelations.RawDivisorBin

end

end OAI
