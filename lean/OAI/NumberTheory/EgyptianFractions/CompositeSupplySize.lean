import OAI.NumberTheory.EgyptianFractions.SupplySize
import OAI.NumberTheory.EgyptianFractions.PrimeProductGrowth

namespace OAI
/-!
# Size of the fourth-power supply for cube-free moduli

The fourth-power auxiliary integer has a controlled logarithmic size.
-/
noncomputable section
open Filter
open scoped BigOperators

namespace Problem337.CompositeSupply

/-- The global divisor pool uses twice the binary logarithm of its range. -/
def primeCount (u : ℕ) : ℕ := ⌈2 * Real.log (u : ℝ) / Real.log 2⌉₊

/-- The product of the first `primeCount u` primes. -/
def base (u : ℕ) : ℕ := primePrefixProduct (primeCount u)

/-- Two powers allow the bilinear products and two powers allow stripping
all small-prime factors of a cube-free modulus. -/
def multiplier (m : ℕ) : ℕ := base (m ^ 4) ^ 4

lemma base_pos (u : ℕ) : 0 < base u := primePrefixProduct_pos _

lemma multiplier_pos (m : ℕ) : 0 < multiplier m := pow_pos (base_pos _) _

lemma primeCount_eq_supplyPrimeCount (u : ℕ) :
    primeCount u = supplyPrimeCount (2 / Real.log 2) u := by
  unfold primeCount supplyPrimeCount
  congr 1
  ring

lemma base_fourth_power (m : ℕ) :
    base (m ^ 4) = primePrefixProduct (supplyPrimeCount (8 / Real.log 2) m) := by
  unfold base primeCount supplyPrimeCount
  rw [Nat.cast_pow, Real.log_pow]
  congr 2
  ring

lemma base_dvd_mono {u v : ℕ} (hu : 0 < u) (huv : u ≤ v) : base u ∣ base v := by
  apply primePrefixProduct_dvd_mono
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ Real.log 2)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  exact Real.log_le_log (by exact_mod_cast hu) (by exact_mod_cast huv)

/-- A prime not dividing the initial prime product is beyond its index cutoff. -/
lemma primeCount_le_of_not_dvd (u p : ℕ) (hp : p.Prime) (hnot : ¬ p ∣ base u) :
    primeCount u ≤ p := by
  by_contra h
  have hplt : p < primeCount u := by omega
  have hi : Nat.count Nat.Prime p < primeCount u :=
    (Nat.count_le Nat.Prime).trans_lt hplt
  have hd := Finset.dvd_prod_of_mem (fun i => Nat.nth Nat.Prime i)
    (Finset.mem_range.mpr hi)
  apply hnot
  simpa only [base, primePrefixProduct, Nat.nth_count hp] using hd

lemma log_le_primeCount (u : ℕ) : Real.log (u : ℝ) ≤ primeCount u := by
  have hl2 : 0 < Real.log 2 := by positivity
  have hl2upper : Real.log 2 ≤ 2 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
  have hlog0 := Real.log_natCast_nonneg u
  have hfirst : Real.log (u : ℝ) ≤ 2 * Real.log (u : ℝ) / Real.log 2 := by
    apply (le_div_iff₀ hl2).mpr
    nlinarith
  exact hfirst.trans (Nat.le_ceil _)

/-- Every residual prime after removing the global pool is genuinely rough. -/
lemma log_le_prime_of_not_dvd (u p : ℕ) (hp : p.Prime) (hnot : ¬ p ∣ base u) :
    Real.log (u : ℝ) ≤ (p : ℝ) :=
  (log_le_primeCount u).trans (by exact_mod_cast primeCount_le_of_not_dvd u p hp hnot)

/-- The full cutoff coefficient is available when a dyadic shell requires
roughness at `log (2*u)` rather than just `log u`. -/
lemma scaled_log_le_prime_of_not_dvd (u p : ℕ) (hp : p.Prime)
    (hnot : ¬ p ∣ base u) :
    2 * Real.log (u : ℝ) / Real.log 2 ≤ (p : ℝ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast primeCount_le_of_not_dvd u p hp hnot)

lemma log_double_le_prime_of_not_dvd (u p : ℕ) (hu : 2 ≤ u) (hp : p.Prime)
    (hnot : ¬ p ∣ base u) : Real.log (2 * (u : ℝ)) ≤ (p : ℝ) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hl2 : 0 < Real.log 2 := by positivity
  have hl2one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlu : Real.log 2 ≤ Real.log (u : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hu)
  have hlu0 : 0 ≤ Real.log (u : ℝ) := Real.log_natCast_nonneg u
  have hscale := scaled_log_le_prime_of_not_dvd u p hp hnot
  have htwo : 2 * Real.log (u : ℝ) ≤ 2 * Real.log (u : ℝ) / Real.log 2 := by
    apply (le_div_iff₀ hl2).mpr
    nlinarith
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) huR.ne']
  linarith

lemma base_squarefree (u : ℕ) : Squarefree (base u) := by
  unfold base primePrefixProduct
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    simp only [← Nat.coprime_iff_isRelPrime]
    apply (Nat.coprime_primes (Nat.prime_nth_prime i) (Nat.prime_nth_prime j)).mpr
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective.ne hij
  · intro i hi
    exact (Nat.prime_nth_prime i).squarefree

/-- The divisor pool has the required quadratic cardinality. -/
lemma square_le_divisors_card (u : ℕ) : u ^ 2 ≤ (base u).divisors.card := by
  unfold base
  rw [card_divisors_primePrefixProduct]
  by_cases hu : u = 0
  · simp [hu]
  have huR : (0 : ℝ) < u := by exact_mod_cast Nat.pos_of_ne_zero hu
  have hlog2 : 0 < Real.log 2 := by positivity
  have hc : 2 * Real.log (u : ℝ) ≤ (primeCount u : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog2).mp (Nat.le_ceil _)
  have hlogs : Real.log ((u : ℝ) ^ 2) ≤
      Real.log ((2 : ℝ) ^ primeCount u) := by
    rw [Real.log_pow, Real.log_pow]
    norm_num
    exact hc
  have hreal : (u : ℝ) ^ 2 ≤ (2 : ℝ) ^ primeCount u :=
    (Real.log_le_log_iff (by positivity) (by positivity)).mp hlogs
  exact_mod_cast hreal

lemma square_le_base (u : ℕ) : u ^ 2 ≤ base u := by
  have h := square_le_divisors_card u
  rw [base, card_divisors_primePrefixProduct] at h
  exact h.trans (two_pow_le_primePrefixProduct _)

lemma marker_lt_multiplier (m : ℕ) (hm : 2 ≤ m) : m < multiplier m := by
  have hm1 : 1 ≤ m := by omega
  have hm_sq : m < m ^ 2 := by nlinarith
  have hm4 : m ^ 2 ≤ m ^ 4 := Nat.pow_le_pow_right hm1 (by norm_num)
  have hu : 1 ≤ m ^ 4 := one_le_pow₀ hm1
  have hbase : m ^ 4 ≤ base (m ^ 4) :=
    (Nat.le_self_pow (by norm_num : 2 ≠ 0) (m ^ 4)).trans (square_le_base _)
  have hp : base (m ^ 4) ≤ base (m ^ 4) ^ 4 := Nat.le_self_pow (by norm_num) _
  exact hm_sq.trans_le (hm4.trans (hbase.trans hp))

/-- Every variable smaller pool nests in the one global pool, including its
fourth power. -/
lemma base_pow_dvd_multiplier {u m : ℕ} (hu : 0 < u) (hum : u ≤ m ^ 4) :
    base u ^ 4 ∣ multiplier m := pow_dvd_pow_of_dvd (base_dvd_mono hu hum) 4

/-- Uniform growth bound for the variable global divisor pool. -/
theorem eventually_log_base_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      Real.log (base u : ℝ) ≤
        (2 / Real.log 2 + ε) * Real.log (u : ℝ) *
          Real.log (Real.log (u : ℝ)) := by
  have hx : Tendsto (fun u : ℕ => Real.log (u : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hprime := hx.eventually (eventually_log_primePrefixProduct_ceil_le
    (2 / Real.log 2) ε (by positivity) hε)
  filter_upwards [hprime] with u hu
  simpa only [base, primeCount_eq_supplyPrimeCount, supplyPrimeCount] using hu

/-- The sharp leading logarithmic size coefficient is the same as in the
original marked construction. No prime-distribution theorem is assumed. -/
theorem eventually_log_multiplier_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (multiplier m : ℝ) ≤
        (32 / Real.log 2 + ε) * Real.log (m : ℝ) *
          Real.log (Real.log (m : ℝ)) := by
  have hx : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hprime := hx.eventually (eventually_log_primePrefixProduct_ceil_le
    (8 / Real.log 2) (ε / 4) (by positivity) (by positivity))
  filter_upwards [hprime] with m hm
  rw [multiplier, base_fourth_power, Nat.cast_pow, Real.log_pow]
  change (4 : ℝ) *
      Real.log (primePrefixProduct ⌈(8 / Real.log 2) * Real.log (m : ℝ)⌉₊ : ℝ) ≤ _
  calc
    _ ≤ 4 * ((8 / Real.log 2 + ε / 4) * Real.log (m : ℝ) *
        Real.log (Real.log (m : ℝ))) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring

end Problem337.CompositeSupply

end

end OAI
