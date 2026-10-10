import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PowersetFirstMoment
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeProductSquarefree
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.OneAddSumLeProduct

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

def subsetCost (f g : ℕ → ℂ) (C B : ℝ) (p : ℕ) : ℝ :=
  1 / (C * Real.log B) + Real.log p / (C * B) + 2 * (1 - ‖f p * g p‖)

lemma subsetCost_nonneg (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g)
    {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) (p : ℕ) :
    0 ≤ subsetCost f g C B p := by
  have hl := Real.log_nonneg hB
  unfold subsetCost
  exact add_nonneg (add_nonneg (by positivity)
    (div_nonneg (Real.log_natCast_nonneg p) (by positivity)))
    (mul_nonneg (by norm_num) (sub_nonneg.mpr (modulus_product_le_one f g hf hg p)))

lemma cost_moment (f g : ℕ → ℂ) (C B : ℝ) :
    (∑ p ∈ core B ∪ center B, primeWeight B p * subsetCost f g C B p / (1+primeWeight B p)) =
      (∑ p ∈ core B ∪ center B, primeWeight B p / (1+primeWeight B p)) / (C*Real.log B) +
      (∑ p ∈ core B ∪ center B, primeWeight B p * Real.log p / (1+primeWeight B p)) / (C*B) +
      2 * ∑ p ∈ core B ∪ center B, primeWeight B p * (1-‖f p*g p‖) / (1+primeWeight B p) := by
  simp only [sum_div, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl (fun p hp => by unfold subsetCost; ring)

lemma exists_small_cost (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (hfd : Summable (primeDefect f)) (hgd : Summable (primeDefect g)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ B : ℝ in atTop, 2 ≤ B ∧
      2 * (∑ p ∈ core B ∪ center B,
        primeWeight B p * subsetCost f g C B p / (1 + primeWeight B p)) ≤ 1 := by
  obtain ⟨K,hK,hKB⟩ := first_moments_bound
  let C := 16*(K+1)
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  filter_upwards [hKB, defect_first_moment_small f g hf hg hfd hgd (1/16) (by norm_num),
    eventually_ge_atTop (2:ℝ)] with B hK' hd hB
  refine ⟨hB, ?_⟩
  have hB0 : 0 < B := by linarith
  have hl : 0 < Real.log B := Real.log_pos (by linarith)
  have hdiv : K/C ≤ 1/16 := by
    apply (div_le_iff₀ hC).mpr
    dsimp [C]
    linarith
  have h1 : (∑ p ∈ core B ∪ center B, primeWeight B p / (1+primeWeight B p)) / (C*Real.log B) ≤ K/C := by
    calc
      _ ≤ (K*Real.log B)/(C*Real.log B) := div_le_div_of_nonneg_right hK'.1 (by positivity)
      _ = K/C := mul_div_mul_right _ _ hl.ne'
  have h2 : (∑ p ∈ core B ∪ center B, primeWeight B p * Real.log p / (1+primeWeight B p)) / (C*B) ≤ K/C := by
    calc
      _ ≤ (K*B)/(C*B) := div_le_div_of_nonneg_right hK'.2 (by positivity)
      _ = K/C := mul_div_mul_right _ _ hB0.ne'
  rw [cost_moment]
  linarith

lemma subset_cost_bounds (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (hmf : Multiplicative f) (hmg : Multiplicative g) (h1f : f 1 = 1) (h1g : g 1 = 1)
    {C B : ℝ} (hC : 0 < C) (hB : 1 < B) (R : Finset ℕ)
    (hR : ∀ p ∈ R, p.Prime) (hc : (∑ p ∈ R, subsetCost f g C B p) ≤ 1) :
    R.card ≤ J C B ∧ Real.log ((∏ p ∈ R, p : ℕ) : ℝ) ≤ C*B ∧
      1/2 ≤ ‖f (∏ p ∈ R, p) * g (∏ p ∈ R, p)‖ := by
  have hs : (∑ p ∈ R, subsetCost f g C B p) =
      (R.card : ℝ) / (C*Real.log B) + (∑ p ∈ R, Real.log p) / (C*B) +
        2*(∑ p ∈ R, (1-‖f p*g p‖)) := by
    simp only [subsetCost, sum_add_distrib, sum_div, sum_const, nsmul_eq_mul, ← mul_sum]
    ring
  rw [hs] at hc
  have hlB := Real.log_pos hB
  have hcard : 0 ≤ (R.card : ℝ) / (C*Real.log B) := by positivity
  have hlog : 0 ≤ (∑ p ∈ R, Real.log p) / (C*B) := by
    exact div_nonneg (sum_nonneg (fun p hp => Real.log_natCast_nonneg p)) (by positivity)
  have hdef : 0 ≤ ∑ p ∈ R, (1-‖f p*g p‖) := sum_nonneg (fun p hp =>
    sub_nonneg.mpr (modulus_product_le_one f g hf hg p))
  refine ⟨?_, ?_, ?_⟩
  · have hcard' : (R.card:ℝ) ≤ C*Real.log B :=
      (div_le_one (mul_pos hC (Real.log_pos hB))).mp (by linarith)
    exact_mod_cast hcard'.trans (Nat.le_ceil _)
  · rw [OrdinaryWindowEuler.log_prod_primes R hR]
    apply (div_le_one (mul_pos hC (by linarith))).mp
    linarith
  · have he := product_modulus_defect f g hf hg hmf hmg h1f h1g R hR
    linarith

lemma truncated_divisor_mass (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (hmf : Multiplicative f) (hmg : Multiplicative g) (h1f : f 1 = 1) (h1g : g 1 = 1)
    (hfd : Summable (primeDefect f)) (hgd : Summable (primeDefect g)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ B : ℝ in atTop, 2 ≤ B ∧
      ∃ D : Finset ℕ,
        (∀ d ∈ D, Squarefree d ∧ d.primeFactors ⊆ core B ∪ center B ∧ 1 < d ∧
          d.primeFactors.card ≤ J C B ∧ Real.log d ≤ C*B ∧ 1/2 ≤ ‖f d * g d‖) ∧
        L₀ B / 4 ≤ ∑ d ∈ D, divisorWeight B d / d := by
  classical
  obtain ⟨C,hC,hCB⟩ := exists_small_cost f g hf hg hfd hgd
  refine ⟨C,hC, ?_⟩
  filter_upwards [hCB, L₀_tendsto.eventually_ge_atTop 4] with B hB hL
  refine ⟨hB.1, ?_⟩
  let U := ((core B ∪ center B).powerset).filter (fun R => (∑ p ∈ R, subsetCost f g C B p) ≤ 1)
  let V := U.erase ∅
  let d : Finset ℕ → ℕ := fun R => ∏ p ∈ R, p
  have hprime (R : Finset ℕ) (hR : R ∈ U) : ∀ p ∈ R, p.Prime := by
    intro p hp
    exact (mem_filter.mp (source_prime_subset B ((mem_powerset.mp (mem_filter.mp hR).1) hp))).2
  have hfactors (R : Finset ℕ) (hR : R ∈ U) : (d R).primeFactors = R := by
    exact Nat.primeFactors_prod (hprime R hR)
  have hdpos (R : Finset ℕ) (hR : R ∈ U) : 0 < d R := prod_pos (fun p hp => (hprime R hR p hp).pos)
  have hinj : Set.InjOn d (↑V : Set (Finset ℕ)) := by
    intro R hR S hS he
    have := congrArg Nat.primeFactors he
    simpa only [hfactors R (mem_of_mem_erase hR), hfactors S (mem_of_mem_erase hS)] using this
  refine ⟨V.image d, ?_, ?_⟩
  · intro n hn
    obtain ⟨R,hR,rfl⟩ := mem_image.mp hn
    have hRU := mem_of_mem_erase hR
    obtain ⟨hcard, hsize, hmod⟩ := subset_cost_bounds f g hf hg hmf hmg h1f h1g
      (by linarith : 0 < C) (by linarith [hB.1] : 1 < B) R (hprime R hRU) (mem_filter.mp hRU).2
    refine ⟨OrdinaryWindowEuler.prime_product_squarefree R (hprime R hRU), ?_, ?_, ?_, hsize, hmod⟩
    · rw [hfactors R hRU]
      exact mem_powerset.mp (mem_filter.mp hRU).1
    · have hn0 := hdpos R hRU
      have hn1 : d R ≠ 1 := by
        intro he
        have := hfactors R hRU
        rw [he, Nat.primeFactors_one] at this
        exact (mem_erase.mp hR).1 this.symm
      omega
    · rwa [hfactors R hRU]
  · have ht := OrdinaryWindowEuler.truncated_mass (core B ∪ center B) (primeWeight B)
      (subsetCost f g C B) (fun p hp => primeWeight_nonneg B p)
      (fun p hp => subsetCost_nonneg f g hf hg (by linarith) (by linarith [hB.1]) p)
      (by norm_num : (0:ℝ)<1) hB.2
    rw [prod_one_add, euler_product] at ht
    have hsumU : (∑ R ∈ U, ∏ p ∈ R, primeWeight B p) =
        ∑ R ∈ (core B ∪ center B).powerset,
          if (∑ p ∈ R, subsetCost f g C B p) ≤ 1 then ∏ p ∈ R, primeWeight B p else 0 := sum_filter _ _
    rw [←hsumU] at ht
    have he : (∑ R ∈ V, ∏ p ∈ R, primeWeight B p) + 1 =
        ∑ R ∈ U, ∏ p ∈ R, primeWeight B p := by
      have hh := sum_erase_add (s := U) (f := fun R => ∏ p ∈ R, primeWeight B p)
        (show ∅ ∈ U by simp [U])
      simpa only [Finset.prod_empty] using hh
    have hv : L₀ B / 4 ≤ ∑ R ∈ V, ∏ p ∈ R, primeWeight B p := by linarith
    rw [sum_image hinj]
    convert hv using 1
    apply sum_congr rfl
    intro R hR
    have hRU := mem_of_mem_erase hR
    have hh := product_primeWeight B (d R) (hdpos R hRU) (by rw [hfactors R hRU])
    rw [hfactors R hRU] at hh
    exact hh.symm

end OrdinaryCorrelations.RawDivisorBin

end

end OAI
