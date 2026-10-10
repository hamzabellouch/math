import OAI.NumberTheory.EgyptianFractions.RationalSupplyReduction
import Mathlib.NumberTheory.Chebyshev

namespace OAI
noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace Problem337

/-- All positive ordered triples of fixed sum, without primality restrictions. -/
def supplyIntegerTriples (u : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 u) ×ˢ ((Finset.Icc 1 u) ×ˢ (Finset.Icc 1 u))).filter
    (fun t => t.1 + t.2.1 + t.2.2 = u)

/-- Logarithmic weight supported only on primes, unlike the von Mangoldt weight. -/
def primeLogWeight (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

/-- The weighted ternary convolution used in the analytic three-prime theorem. -/
def mangoldtTripleSum (u : ℕ) : ℝ :=
  ∑ t ∈ supplyIntegerTriples u,
    ArithmeticFunction.vonMangoldt t.1 * ArithmeticFunction.vonMangoldt t.2.1 *
      ArithmeticFunction.vonMangoldt t.2.2

/-- The corresponding weighted sum over genuine prime triples. -/
def primeTripleLogSum (u : ℕ) : ℝ :=
  ∑ t ∈ supplyPrimeTriples u,
    Real.log (t.1 : ℝ) * Real.log (t.2.1 : ℝ) * Real.log (t.2.2 : ℝ)

lemma primeLogWeight_nonneg (n : ℕ) : 0 ≤ primeLogWeight n := by
  unfold primeLogWeight
  split_ifs with hn
  · exact Real.log_nonneg (by exact_mod_cast hn.one_le)
  · exact le_rfl

lemma primeLogWeight_le_vonMangoldt (n : ℕ) :
    primeLogWeight n ≤ ArithmeticFunction.vonMangoldt n := by
  unfold primeLogWeight
  split_ifs with hn
  · exact (ArithmeticFunction.vonMangoldt_apply_prime hn).ge
  · exact ArithmeticFunction.vonMangoldt_nonneg

lemma primeTripleLogSum_eq (u : ℕ) :
    primeTripleLogSum u = ∑ t ∈ supplyIntegerTriples u,
      primeLogWeight t.1 * primeLogWeight t.2.1 * primeLogWeight t.2.2 := by
  classical
  have hset : supplyPrimeTriples u = (supplyIntegerTriples u).filter
      (fun t => t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime) := by
    ext t
    simp only [supplyPrimeTriples, supplyIntegerTriples, Finset.mem_filter]
    tauto
  unfold primeTripleLogSum
  rw [hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases h1 : t.1.Prime <;> by_cases h2 : t.2.1.Prime <;>
    by_cases h3 : t.2.2.Prime <;> simp [primeLogWeight, h1, h2, h3]

/-- A weighted version of the fixed-coordinate counting bound. -/
lemma fixed_sum_coordinate_sum_le
    {α : Type*} [DecidableEq α] (T : Finset α) (U : Finset ℕ)
    (x y z : α → ℕ) (u : ℕ) (f : ℕ → ℝ)
    (hf : ∀ n ∈ U, 0 ≤ f n)
    (hsum : ∀ t ∈ T, x t + y t + z t = u)
    (hU : ∀ t ∈ T, x t ∈ U ∧ y t ∈ U)
    (hinj : Function.Injective (fun t => (x t, y t, z t))) :
    (∑ t ∈ T, f (x t)) ≤ (U.card : ℝ) * ∑ n ∈ U, f n := by
  classical
  have hi : Set.InjOn (fun t => (x t, y t)) (T : Set α) := by
    intro a ha b hb hab
    have hxy := Prod.mk.inj hab
    have hz : z a = z b := by
      have := hsum a ha
      have := hsum b hb
      omega
    exact hinj (Prod.ext hxy.1 (Prod.ext hxy.2 hz))
  have hsub : T.image (fun t => (x t, y t)) ⊆ U ×ˢ U := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr (hU t ht)
  calc
    (∑ t ∈ T, f (x t)) = ∑ q ∈ T.image (fun t => (x t, y t)), f q.1 := by
      rw [Finset.sum_image]
      exact hi
    _ ≤ ∑ q ∈ U ×ˢ U, f q.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro q hq _
      exact hf q.1 (Finset.mem_product.mp hq).1
    _ = (U.card : ℝ) * ∑ n ∈ U, f n := by
      rw [Finset.sum_product]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum]

/-- Prime powers of exponent at least two carry exactly the difference of the
Chebyshev functions. -/
lemma sum_primePowerLogWeight (u : ℕ) :
    (∑ n ∈ Finset.Icc 1 u,
      (ArithmeticFunction.vonMangoldt n - primeLogWeight n)) =
        Chebyshev.psi u - Chebyshev.theta u := by
  rw [Finset.sum_sub_distrib]
  congr 1
  · simp only [Chebyshev.psi, Nat.floor_natCast]
    congr 1
  · simp only [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter,
      primeLogWeight]
    congr 1

private lemma triple_product_difference_le
    (a b c p q r L : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hpa : p ≤ a) (hqb : q ≤ b) (hrc : r ≤ c)
    (ha : a ≤ L) (hb : b ≤ L) (hc : c ≤ L) :
    a * b * c ≤ p * q * r + L ^ 2 * ((a - p) + (b - q) + (c - r)) := by
  have hL : 0 ≤ L := hp.trans (hpa.trans ha)
  have ha0 := hp.trans hpa
  have hb0 := hq.trans hqb
  have hc0 := hr.trans hrc
  have hpL := hpa.trans ha
  have hqL := hqb.trans hb
  have h1 : (a - p) * b * c ≤ (a - p) * L * L := by gcongr
  have h2 : p * (b - q) * c ≤ L * (b - q) * L := by gcongr
  have h3 : p * q * (c - r) ≤ L * L * (c - r) := by gcongr
  nlinarith

lemma mangoldtTripleSum_le_primeTripleLogSum (u : ℕ) :
    mangoldtTripleSum u ≤ primeTripleLogSum u +
      3 * (u : ℝ) * Real.log (u : ℝ) ^ 2 *
        (Chebyshev.psi u - Chebyshev.theta u) := by
  classical
  let U := Finset.Icc 1 u
  let T := supplyIntegerTriples u
  let d : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n - primeLogWeight n
  have hd (n : ℕ) : 0 ≤ d n := sub_nonneg.mpr (primeLogWeight_le_vonMangoldt n)
  have hT (t : ℕ × ℕ × ℕ) (ht : t ∈ T) :
      t.1 ∈ U ∧ t.2.1 ∈ U ∧ t.2.2 ∈ U := by
    obtain ⟨ht, _⟩ := Finset.mem_filter.mp ht
    exact (Finset.mem_product.mp ht).imp_right Finset.mem_product.mp
  have hsum (t : ℕ × ℕ × ℕ) (ht : t ∈ T) :
      t.1 + t.2.1 + t.2.2 = u := (Finset.mem_filter.mp ht).2
  have hweight (n : ℕ) (hn : n ∈ U) :
      ArithmeticFunction.vonMangoldt n ≤ Real.log (u : ℝ) := by
    apply ArithmeticFunction.vonMangoldt_le_log.trans
    apply Real.log_le_log
    · exact_mod_cast (Finset.mem_Icc.mp hn).1
    · exact_mod_cast (Finset.mem_Icc.mp hn).2
  have h1 := fixed_sum_coordinate_sum_le T U (fun t => t.1)
    (fun t => t.2.1) (fun t => t.2.2) u d (fun n _ => hd n)
    hsum (fun t ht => ⟨(hT t ht).1, (hT t ht).2.1⟩)
    (by intro a b h; exact h)
  have h2 := fixed_sum_coordinate_sum_le T U (fun t => t.2.1)
    (fun t => t.1) (fun t => t.2.2) u d (fun n _ => hd n)
    (by intro t ht; have := hsum t ht; omega)
    (fun t ht => ⟨(hT t ht).2.1, (hT t ht).1⟩)
    (by
      intro a b h
      have hc := Prod.mk.inj h
      have hh := Prod.mk.inj hc.2
      exact Prod.ext hh.1 (Prod.ext hc.1 hh.2))
  have h3 := fixed_sum_coordinate_sum_le T U (fun t => t.2.2)
    (fun t => t.1) (fun t => t.2.1) u d (fun n _ => hd n)
    (by intro t ht; have := hsum t ht; omega)
    (fun t ht => ⟨(hT t ht).2.2, (hT t ht).1⟩)
    (by
      intro a b h
      have hc := Prod.mk.inj h
      have hh := Prod.mk.inj hc.2
      exact Prod.ext hh.1 (Prod.ext hh.2 hc.1))
  have hUcard : U.card = u := by simp [U, Nat.card_Icc]
  have hdSum : (∑ n ∈ U, d n) = Chebyshev.psi u - Chebyshev.theta u :=
    sum_primePowerLogWeight u
  rw [hUcard, hdSum] at h1 h2 h3
  have hlocal : mangoldtTripleSum u ≤ primeTripleLogSum u +
      Real.log (u : ℝ) ^ 2 *
        ((∑ t ∈ T, d t.1) + (∑ t ∈ T, d t.2.1) + (∑ t ∈ T, d t.2.2)) := by
    calc
      mangoldtTripleSum u ≤ ∑ t ∈ T,
          (primeLogWeight t.1 * primeLogWeight t.2.1 * primeLogWeight t.2.2 +
            Real.log (u : ℝ) ^ 2 * (d t.1 + d t.2.1 + d t.2.2)) := by
        apply Finset.sum_le_sum
        intro t ht
        have htU := hT t ht
        exact triple_product_difference_le
          (ArithmeticFunction.vonMangoldt t.1) (ArithmeticFunction.vonMangoldt t.2.1)
          (ArithmeticFunction.vonMangoldt t.2.2) (primeLogWeight t.1)
          (primeLogWeight t.2.1) (primeLogWeight t.2.2) (Real.log u)
          (primeLogWeight_nonneg _) (primeLogWeight_nonneg _) (primeLogWeight_nonneg _)
          (primeLogWeight_le_vonMangoldt _) (primeLogWeight_le_vonMangoldt _)
          (primeLogWeight_le_vonMangoldt _) (hweight _ htU.1)
          (hweight _ htU.2.1) (hweight _ htU.2.2)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_add_distrib, primeTripleLogSum_eq, T]
  have htotal := add_le_add (add_le_add h1 h2) h3
  have hm := mul_le_mul_of_nonneg_left htotal (sq_nonneg (Real.log (u : ℝ)))
  nlinarith

/-- The contribution from genuine higher prime powers is lower order than the
quadratic main term. This uses Mathlib's elementary `ψ - θ = O(sqrt x)` bound. -/
theorem mangoldt_triple_error_isLittleO :
    (fun x : ℝ => 3 * x * Real.log x ^ 2 *
      (Chebyshev.psi x - Chebyshev.theta x)) =o[atTop] (fun x : ℝ => x ^ 2) := by
  have hlog : (fun x : ℝ => Real.log x ^ 2) =o[atTop]
      (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
    simpa only [Real.rpow_two] using
      isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
  have hsmall := hlog.mul_isBigO Chebyshev.isBigO_psi_sub_theta_sqrt
  have hscaled := hsmall.mul_isBigO (isBigO_refl (fun x : ℝ => x) atTop)
  have hquadratic :
      (fun x : ℝ => x * Real.log x ^ 2 * (Chebyshev.psi x - Chebyshev.theta x))
        =o[atTop] (fun x : ℝ => x ^ 2) := by
    apply hscaled.congr'
    · exact Eventually.of_forall (fun x => by simp only [Pi.sub_apply]; ring)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
      norm_num
      ring
  simpa only [mul_assoc] using hquadratic.const_mul_left 3

/-- Explicit error absorption along the natural-number parameter. -/
theorem eventually_mangoldt_triple_error_lt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      3 * (u : ℝ) * Real.log (u : ℝ) ^ 2 *
        (Chebyshev.psi u - Chebyshev.theta u) < ε * (u : ℝ) ^ 2 := by
  have hsmall := mangoldt_triple_error_isLittleO.bound (show 0 < ε / 2 by positivity)
  have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmall
  filter_upwards [hn, eventually_ge_atTop (1 : ℕ)] with u hu hu1
  rw [Real.norm_of_nonneg (sq_nonneg (u : ℝ))] at hu
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu1
  exact (le_trans (le_abs_self _) hu).trans_lt (by nlinarith [sq_pos_of_pos hu0])

/-- An analytic quadratic lower bound for the von Mangoldt convolution implies
one for the prime-only weighted sum. No analytic lower bound is asserted here. -/
theorem weighted_prime_lower_bound_of_mangoldt
    (c : ℝ) (hc : 0 < c)
    (hmain : ∀ᶠ u : ℕ in atTop, Odd u → c * (u : ℝ) ^ 2 ≤ mangoldtTripleSum u) :
    ∀ᶠ u : ℕ in atTop, Odd u →
      (c / 2) * (u : ℝ) ^ 2 ≤ primeTripleLogSum u := by
  filter_upwards [hmain, eventually_mangoldt_triple_error_lt (c / 2) (by positivity)]
    with u hu herr
  intro hodd
  have hupper := mangoldtTripleSum_le_primeTripleLogSum u
  have hlower := hu hodd
  linarith

end Problem337

end

end OAI
