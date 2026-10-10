import OAI.NumberTheory.EgyptianFractions.PrimeTripleAsymptotics
import OAI.NumberTheory.EgyptianFractions.PrimeProductBound

namespace OAI
noncomputable section
open Filter
open scoped Topology BigOperators

namespace Problem337

/-- Chebyshev's elementary bounds give the lower prime-density estimate needed
for the size of the first-prime product. No prime number theorem is used. -/
lemma eventually_primeCounting_ge_linear_div_log :
    ∀ᶠ x : ℝ in atTop,
      (Real.log 2 / 2) * x / Real.log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := eventually_log_pow_lt_mul_rpow 1 1 (Real.log 2 / 4)
    (by norm_num) (by positivity)
  filter_upwards [hsmall, eventually_ge_atTop (8 : ℝ)] with x hlog hx
  simp only [pow_one, Real.rpow_one] at hlog
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hlogadd : Real.log (x + 2) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  apply le_trans ?_ (Chebyshev.pi_ge' hx1)
  apply div_le_div_of_nonneg_right _ (Real.log_pos hx1).le
  nlinarith

lemma eventually_nth_prime_le_rpow (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (Nat.nth Nat.Prime n : ℝ) ≤ (n : ℝ) ^ (1 + δ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : 0 < 1 + δ := by linarith
  have hsmall := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ))
    atTop atTop).eventually (eventually_log_pow_lt_mul_rpow 1 δ
      (Real.log 2 / (2 * (1 + δ))) hδ (by positivity))
  have hpcount := ((tendsto_rpow_atTop he).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually
      eventually_primeCounting_ge_linear_div_log
  filter_upwards [hsmall, hpcount, eventually_ge_atTop 2] with n hn hp hn2
  simp only [Function.comp_apply] at hp
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := lt_trans zero_lt_one hnR
  have hx1 : (1 : ℝ) < (n : ℝ) ^ (1 + δ) := Real.one_lt_rpow hnR he
  have hlogpow : Real.log ((n : ℝ) ^ (1 + δ)) = (1 + δ) * Real.log (n : ℝ) :=
    Real.log_rpow hn0 _
  have hpow : (n : ℝ) ^ (1 + δ) = (n : ℝ) * (n : ℝ) ^ δ := by
    rw [Real.rpow_add hn0, Real.rpow_one]
  have hcount : (n : ℝ) < (Nat.primeCounting ⌊(n : ℝ) ^ (1 + δ)⌋₊ : ℝ) := by
    apply lt_of_lt_of_le _ hp
    apply (lt_div_iff₀ (Real.log_pos hx1)).2
    rw [hlogpow, hpow]
    simp only [pow_one] at hn
    have ht := (lt_div_iff₀ (show 0 < 2 * (1 + δ) by positivity)).1
      (show Real.log (n : ℝ) <
        (Real.log 2 * (n : ℝ) ^ δ) / (2 * (1 + δ)) by convert hn using 1; ring)
    nlinarith [mul_lt_mul_of_pos_left ht hn0]
  have hcountN : n < Nat.primeCounting ⌊(n : ℝ) ^ (1 + δ)⌋₊ := by exact_mod_cast hcount
  have hnth : Nat.nth Nat.Prime n < ⌊(n : ℝ) ^ (1 + δ)⌋₊ + 1 :=
    Nat.nth_lt_of_lt_count hcountN
  have hnth' : Nat.nth Nat.Prime n ≤ ⌊(n : ℝ) ^ (1 + δ)⌋₊ := by omega
  exact (by exact_mod_cast hnth' : (Nat.nth Nat.Prime n : ℝ) ≤
    (⌊(n : ℝ) ^ (1 + δ)⌋₊ : ℝ)).trans (Nat.floor_le (by positivity))

lemma primePrefixProduct_dvd_of_le {m n : ℕ} (h : m ≤ n) :
    primePrefixProduct m ∣ primePrefixProduct n :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono h)

/-- The sharp leading coefficient in the logarithm of a prime-prefix product
needs only Chebyshev's lower prime-counting estimate. -/
lemma eventually_log_primePrefixProduct_le_growth (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (primePrefixProduct n : ℝ) ≤ (1 + δ) * (n : ℝ) * Real.log (n : ℝ) := by
  filter_upwards [eventually_nth_prime_le_rpow δ hδ, eventually_ge_atTop 2] with n hn hn2
  have hn0 : (0 : ℝ) < n := by positivity
  have hprime0 (i : ℕ) : (0 : ℝ) < Nat.nth Nat.Prime i := by
    exact_mod_cast (Nat.prime_nth_prime i).pos
  have hlog : Real.log (Nat.nth Nat.Prime n : ℝ) ≤ (1 + δ) * Real.log (n : ℝ) := by
    simpa [Real.log_rpow hn0] using Real.log_le_log (hprime0 n) hn
  calc
    Real.log (primePrefixProduct n : ℝ) =
        ∑ i ∈ Finset.range n, Real.log (Nat.nth Nat.Prime i : ℝ) := by
      simp only [primePrefixProduct, Nat.cast_prod]
      exact Real.log_prod (fun i _ => (hprime0 i).ne')
    _ ≤ ∑ _i ∈ Finset.range n, Real.log (Nat.nth Nat.Prime n : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Real.log_le_log (hprime0 i)
      exact_mod_cast (Nat.nth_monotone Nat.infinite_setOfPred_prime)
        (Finset.mem_range.1 hi).le
    _ = (n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ) := by simp
    _ ≤ (n : ℝ) * ((1 + δ) * Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left hlog hn0.le
    _ = (1 + δ) * (n : ℝ) * Real.log (n : ℝ) := by ring

lemma tendsto_log_natCeil_mul_div_log (A : ℝ) (hA : 0 < A) :
    Tendsto (fun x : ℝ => Real.log (⌈A * x⌉₊ : ℝ) / Real.log x)
      atTop (𝓝 1) := by
  have hceil : Tendsto (fun x : ℝ => (⌈A * x⌉₊ : ℝ) / x) atTop (𝓝 A) :=
    tendsto_nat_ceil_mul_div_atTop hA.le
  have hz := (hceil.log hA.ne').div_atTop Real.tendsto_log_atTop
  have hlim : Tendsto (fun x : ℝ => 1 + Real.log ((⌈A * x⌉₊ : ℝ) / x) / Real.log x)
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.add hz
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hc0 : (0 : ℝ) < ⌈A * x⌉₊ := (mul_pos hA hx0).trans_le (Nat.le_ceil _)
  rw [Real.log_div hc0.ne' hx0.ne']
  field_simp [(Real.log_pos hx).ne']; ring

/-- A directly usable prime-product bound at the logarithmic number of primes
required by rational-divisor supply. -/
lemma eventually_log_primePrefixProduct_ceil_le (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      Real.log (primePrefixProduct ⌈A * x⌉₊ : ℝ) ≤ (A + ε) * x * Real.log x := by
  let δ : ℝ := ε / (2 * A)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hceil : Tendsto (fun x : ℝ => (⌈A * x⌉₊ : ℝ) / x) atTop (𝓝 A) :=
    tendsto_nat_ceil_mul_div_atTop hA.le
  have hratio : Tendsto (fun x : ℝ =>
      ((1 + δ) * (⌈A * x⌉₊ : ℝ) * Real.log (⌈A * x⌉₊ : ℝ)) /
        (x * Real.log x)) atTop (𝓝 ((1 + δ) * A)) := by
    have h := (hceil.const_mul (1 + δ)).mul (tendsto_log_natCeil_mul_div_log A hA)
    convert h using 1
    · ext x
      ring
    · simp
  have hcoef : (1 + δ) * A < A + ε := by
    dsimp [δ]
    field_simp
    nlinarith
  have hell : Tendsto (fun x : ℝ => ⌈A * x⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp (tendsto_id.const_mul_atTop hA)
  have hprod := hell.eventually (eventually_log_primePrefixProduct_le_growth δ hδ)
  filter_upwards [hratio.eventually (gt_mem_nhds hcoef), hprod,
    eventually_gt_atTop (1 : ℝ)] with x hr hp hx
  have hden : 0 < x * Real.log x := mul_pos (lt_trans zero_lt_one hx) (Real.log_pos hx)
  exact hp.trans (by simpa only [mul_assoc] using ((div_lt_iff₀ hden).1 hr).le)

lemma log_factorial_natFloor_le_sq (x : ℝ) (hx : 0 ≤ x) :
    Real.log ((⌊x⌋₊.factorial : ℕ) : ℝ) ≤ x ^ 2 := by
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hlog := Real.log_le_log (by exact_mod_cast Nat.factorial_pos ⌊x⌋₊)
    (show ((⌊x⌋₊.factorial : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) ^ ⌊x⌋₊ by
      exact_mod_cast Nat.factorial_le_pow ⌊x⌋₊)
  rw [Real.log_pow] at hlog
  have hself := Real.log_le_self (Nat.cast_nonneg ⌊x⌋₊ : (0 : ℝ) ≤ ⌊x⌋₊)
  nlinarith [mul_le_mul_of_nonneg_left hself (Nat.cast_nonneg ⌊x⌋₊ : (0 : ℝ) ≤ ⌊x⌋₊)]

/-- The supply multiplier from the marked-denominator construction, with the
prime count already simplified using `log (m^4) = 4 log m`. -/
def markedSupplyMultiplier (m : ℕ) : ℕ :=
  primePrefixProduct ⌈(16 / Real.log 2) * Real.log (m : ℝ)⌉₊ ^ 2 *
    ⌊Real.log (Real.log (m : ℝ))⌋₊.factorial

lemma markedSupplyMultiplier_pos (m : ℕ) : 0 < markedSupplyMultiplier m := by
  exact Nat.mul_pos (pow_pos (primePrefixProduct_pos _) _) (Nat.factorial_pos _)

lemma eventually_log_markedSupplyMultiplier_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (markedSupplyMultiplier m : ℝ) ≤
        (32 / Real.log 2 + ε) * Real.log (m : ℝ) * Real.log (Real.log (m : ℝ)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogtop : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hprime := hlogtop.eventually
    (eventually_log_primePrefixProduct_ceil_le (16 / Real.log 2) (ε / 4)
      (by positivity) (by positivity))
  have hsmall := hlogtop.eventually
    (eventually_log_pow_lt_mul_rpow 1 1 (ε / 2) (by norm_num) (by positivity))
  filter_upwards [hprime, hsmall, hlogtop.eventually (eventually_ge_atTop (1 : ℝ))]
    with m hp hs hm
  have hL : 0 ≤ Real.log (Real.log (m : ℝ)) := Real.log_nonneg hm
  have hfact := log_factorial_natFloor_le_sq (Real.log (Real.log (m : ℝ))) hL
  simp only [pow_one, Real.rpow_one] at hs
  have hbudget : Real.log ((⌊Real.log (Real.log (m : ℝ))⌋₊.factorial : ℕ) : ℝ) ≤
      (ε / 2) * Real.log (m : ℝ) * Real.log (Real.log (m : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_right hs.le hL]
  have hPpos : (0 : ℝ) < primePrefixProduct ⌈(16 / Real.log 2) * Real.log (m : ℝ)⌉₊ := by
    exact_mod_cast primePrefixProduct_pos ⌈(16 / Real.log 2) * Real.log (m : ℝ)⌉₊
  have hFpos : (0 : ℝ) < ⌊Real.log (Real.log (m : ℝ))⌋₊.factorial := by
    exact_mod_cast Nat.factorial_pos ⌊Real.log (Real.log (m : ℝ))⌋₊
  rw [markedSupplyMultiplier, Nat.cast_mul, Nat.cast_pow,
    Real.log_mul (by positivity) hFpos.ne', Real.log_pow]
  norm_num
  calc
    2 * Real.log (primePrefixProduct ⌈16 / Real.log 2 * Real.log (m : ℝ)⌉₊ : ℝ) +
        Real.log (⌊Real.log (Real.log (m : ℝ))⌋₊.factorial : ℝ) ≤
      2 * ((16 / Real.log 2 + ε / 4) * Real.log (m : ℝ) * Real.log (Real.log (m : ℝ))) +
        (ε / 2) * Real.log (m : ℝ) * Real.log (Real.log (m : ℝ)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num)) hbudget
    _ = (32 / Real.log 2 + ε) * Real.log (m : ℝ) * Real.log (Real.log (m : ℝ)) := by ring

lemma lt_markedSupplyMultiplier (m : ℕ) (hm : 2 ≤ m) : m < markedSupplyMultiplier m := by
  let n : ℕ := ⌈(16 / Real.log 2) * Real.log (m : ℝ)⌉₊
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hm1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : (16 / Real.log 2) * Real.log (m : ℝ) ≤ (n : ℝ) := Nat.le_ceil _
  have h16 : 16 * Real.log (m : ℝ) ≤ (n : ℝ) * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_right hceil hl2.le
    calc
      16 * Real.log (m : ℝ) =
          ((16 / Real.log 2) * Real.log (m : ℝ)) * Real.log 2 := by field_simp
      _ ≤ (n : ℝ) * Real.log 2 := hmul
  have hlow := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)
    (show (2 : ℝ) ^ n ≤ (primePrefixProduct n : ℝ) by
      exact_mod_cast two_pow_le_primePrefixProduct n)
  rw [Real.log_pow] at hlow
  have hPl : Real.log (m : ℝ) < Real.log (primePrefixProduct n : ℝ) := by linarith
  have hmP : m < primePrefixProduct n := by
    exact_mod_cast (Real.log_lt_log_iff (by positivity : (0 : ℝ) < m)
      (by exact_mod_cast primePrefixProduct_pos n)).1 hPl
  have hPpower : primePrefixProduct n ≤ primePrefixProduct n ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  have hpower : primePrefixProduct n ^ 2 ≤ markedSupplyMultiplier m := by
    apply Nat.le_mul_of_pos_right
    exact Nat.factorial_pos _
  exact hmP.trans_le (hPpower.trans hpower)

end Problem337

end

end OAI
