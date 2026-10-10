import OAI.NumberTheory.EgyptianFractions.HitCount
import OAI.NumberTheory.EgyptianFractions.PrimeGcdHits
import OAI.NumberTheory.EgyptianFractions.PrimeHits

namespace OAI
open scoped BigOperators

namespace Problem337.RandomProducts

/-- A concrete large-gcd probability estimate for uniform samples from a prime set.
This retains all sample multiplicities, and uses only finite counting. -/
theorem large_gcd_probability_le_exp (P : Finset ℕ) (t u : ℕ) (S V : ℝ)
    (hP : P.Nonempty) (hS : 1 < S) (hV : 0 ≤ V)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hmax : ∀ p ∈ P, (p : ℝ) ≤ S ^ 101)
    (ht : (t : ℝ) ≤ S) (hhits : ((P.filter (fun p => p ∣ u)).card : ℝ) ≤ S)
    (hsize : S ^ 99 ≤ (P.card : ℝ)) :
    (((sampleWords P t).filter (fun f =>
      Real.exp ((2 / 25 : ℝ) * V) < (Nat.gcd (∏ i, f i) u : ℝ))).card : ℝ) /
        (P.card : ℝ) ^ t ≤ Real.exp (-V / 20) := by
  classical
  let k : ℕ := ⌈((2 / 25 : ℝ) * V) / (101 * Real.log S)⌉₊
  let H := P.filter (fun p => p ∣ u)
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hk : ((2 / 25 : ℝ) * V) / (101 * Real.log S) ≤ (k : ℝ) := Nat.le_ceil _
  have hknum : 8 * V ≤ 10100 * (k : ℝ) * Real.log S := by
    have h := (div_le_iff₀ (by positivity : 0 < 101 * Real.log S)).mp hk
    nlinarith
  have hsub : (sampleWords P t).filter (fun f =>
      Real.exp ((2 / 25 : ℝ) * V) < (Nat.gcd (∏ i, f i) u : ℝ)) ⊆
      hitWords P H t k := by
    intro f hf
    obtain ⟨hfP, hlarge⟩ := Finset.mem_filter.mp hf
    have hfp : ∀ i, f i ∈ P := Fintype.mem_piFinset.mp hfP
    have hB : 1 < S ^ 101 := one_lt_pow₀ hS (by decide)
    have hcount := hit_count_large_of_gcd_large Finset.univ f u
      (fun i _ => hprime (f i) (hfp i)) (fun i _ => hmax (f i) (hfp i))
      hB (Real.exp_pos _) hlarge
    have hratio : ((2 / 25 : ℝ) * V) / (101 * Real.log S) <
        ((Finset.univ.filter (fun i => f i ∣ u)).card : ℝ) := by
      simpa only [Real.log_exp, Real.log_pow, Nat.cast_ofNat] using hcount
    have hkcount : k ≤ (Finset.univ.filter (fun i => f i ∣ u)).card :=
      Nat.ceil_le.mpr hratio.le
    apply Finset.mem_filter.mpr
    refine ⟨hfP, ?_⟩
    have heq : (Finset.univ.filter (fun i => f i ∈ H)) =
        (Finset.univ.filter (fun i => f i ∣ u)) := by
      ext i
      simp only [H, Finset.mem_filter, Finset.mem_univ, true_and, hfp i]
    rw [heq]
    exact hkcount
  calc
    _ ≤ ((hitWords P H t k).card : ℝ) / (P.card : ℝ) ^ t := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ Real.exp (-V / 20) := hit_probability_le_exp P H t k S V hP hS hV ht hhits hsize hknum

/-- The same estimate permits a small fixed frequency factor in the gcd. -/
theorem large_frequency_gcd_probability_le_exp (P : Finset ℕ) (t u l : ℕ) (S V : ℝ)
    (hP : P.Nonempty) (hS : 1 < S) (hV : 0 ≤ V)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hmax : ∀ p ∈ P, (p : ℝ) ≤ S ^ 101)
    (ht : (t : ℝ) ≤ S) (hhits : ((P.filter (fun p => p ∣ u)).card : ℝ) ≤ S)
    (hsize : S ^ 99 ≤ (P.card : ℝ)) (hl : 0 < l)
    (hlbound : (l : ℝ) ≤ Real.exp (V / 200)) :
    (((sampleWords P t).filter (fun f =>
      Real.exp (V / 10) < (Nat.gcd (l * ∏ i, f i) u : ℝ))).card : ℝ) /
        (P.card : ℝ) ^ t ≤ Real.exp (-V / 20) := by
  classical
  have hsub : (sampleWords P t).filter (fun f =>
      Real.exp (V / 10) < (Nat.gcd (l * ∏ i, f i) u : ℝ)) ⊆
      (sampleWords P t).filter (fun f =>
      Real.exp ((2 / 25 : ℝ) * V) < (Nat.gcd (∏ i, f i) u : ℝ)) := by
    intro f hf
    obtain ⟨hfP, hlarge⟩ := Finset.mem_filter.mp hf
    refine Finset.mem_filter.mpr ⟨hfP, ?_⟩
    have hfp : ∀ i, f i ∈ P := Fintype.mem_piFinset.mp hfP
    have hprod : 0 < ∏ i, f i := Finset.prod_pos (fun i _ => (hprime (f i) (hfp i)).pos)
    have hg : 0 < Nat.gcd (∏ i, f i) u := Nat.gcd_pos_of_pos_left u hprod
    have hdiv : Nat.gcd (l * ∏ i, f i) u ∣ l * Nat.gcd (∏ i, f i) u :=
      (Nat.gcd_mul_left_dvd_mul_gcd u l (∏ i, f i)).trans
        (Nat.mul_dvd_mul (Nat.gcd_dvd_left l u) dvd_rfl)
    have hnat := Nat.le_of_dvd (Nat.mul_pos hl hg) hdiv
    have hreal : (Nat.gcd (l * ∏ i, f i) u : ℝ) ≤
        (l : ℝ) * (Nat.gcd (∏ i, f i) u : ℝ) := by exact_mod_cast hnat
    by_contra hnot
    have hsmall := le_of_not_gt hnot
    have hcontr : (Nat.gcd (l * ∏ i, f i) u : ℝ) ≤ Real.exp (V / 10) := by
      calc
        _ ≤ (l : ℝ) * (Nat.gcd (∏ i, f i) u : ℝ) := hreal
        _ ≤ Real.exp (V / 200) * Real.exp ((2 / 25 : ℝ) * V) :=
          mul_le_mul hlbound hsmall (Nat.cast_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (V / 200 + (2 / 25 : ℝ) * V) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (V / 10) := Real.exp_le_exp.mpr (by linarith)
    exact hlarge.not_ge hcontr
  calc
    _ ≤ (((sampleWords P t).filter (fun f =>
        Real.exp ((2 / 25 : ℝ) * V) < (Nat.gcd (∏ i, f i) u : ℝ))).card : ℝ) /
          (P.card : ℝ) ^ t := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ Real.exp (-V / 20) :=
      large_gcd_probability_le_exp P t u S V hP hS hV hprime hmax ht hhits hsize

/-- Reduced moduli below `exp (0.9 V)` form an exponentially small set of samples.
This is the random-gcd estimate used before applying bilinear Fourier cancellation. -/
theorem small_reduced_modulus_probability_le (P : Finset ℕ) (t u l : ℕ) (S V : ℝ)
    (hP : P.Nonempty) (hS : 1 < S) (hV : 0 ≤ V) (huexp : (u : ℝ) = Real.exp V)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hmax : ∀ p ∈ P, (p : ℝ) ≤ S ^ 101)
    (ht : (t : ℝ) ≤ S) (hhits : ((P.filter (fun p => p ∣ u)).card : ℝ) ≤ S)
    (hsize : S ^ 99 ≤ (P.card : ℝ)) (hl : 0 < l)
    (hlbound : (l : ℝ) ≤ Real.exp (V / 200)) :
    (((sampleWords P t).filter (fun f =>
      ((u / Nat.gcd (l * ∏ i, f i) u : ℕ) : ℝ) < Real.exp (9 * V / 10))).card : ℝ) /
        (P.card : ℝ) ^ t ≤ Real.exp (-V / 20) := by
  classical
  have huR : 0 < (u : ℝ) := by rw [huexp]; exact Real.exp_pos _
  have hu : 0 < u := by exact_mod_cast huR
  have hsub : (sampleWords P t).filter (fun f =>
      ((u / Nat.gcd (l * ∏ i, f i) u : ℕ) : ℝ) < Real.exp (9 * V / 10)) ⊆
      (sampleWords P t).filter (fun f =>
      Real.exp (V / 10) < (Nat.gcd (l * ∏ i, f i) u : ℝ)) := by
    intro f hf
    obtain ⟨hfP, hsmall⟩ := Finset.mem_filter.mp hf
    refine Finset.mem_filter.mpr ⟨hfP, ?_⟩
    have hg : 0 < Nat.gcd (l * ∏ i, f i) u := Nat.gcd_pos_of_pos_right _ hu
    have hgR : 0 < (Nat.gcd (l * ∏ i, f i) u : ℝ) := by exact_mod_cast hg
    rw [Nat.cast_div_charZero (Nat.gcd_dvd_right _ _), huexp] at hsmall
    have hmul := (div_lt_iff₀ hgR).mp hsmall
    by_contra hnot
    have hle := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) (Real.exp_pos (9 * V / 10)).le
    have heq : Real.exp (9 * V / 10) * Real.exp (V / 10) = Real.exp V := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq] at hle
    exact hmul.not_ge hle
  calc
    _ ≤ (((sampleWords P t).filter (fun f =>
        Real.exp (V / 10) < (Nat.gcd (l * ∏ i, f i) u : ℝ))).card : ℝ) /
          (P.card : ℝ) ^ t := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ Real.exp (-V / 20) := large_frequency_gcd_probability_le_exp
      P t u l S V hP hS hV hprime hmax ht hhits hsize hl hlbound

/-- The random-gcd bound with exactly the prime sampling scale used in the manuscript.
No asymptotic number-theory result is hidden: existence and cardinality of the prime set
are explicit hypotheses, while the entire exceptional-event estimate is proved. -/
theorem random_gcd_exception_bound (P : Finset ℕ) (t u l : ℕ) (S V : ℝ)
    (hP : P.Nonempty) (hS : 2 ≤ S) (hV : 0 ≤ V) (hVS : V ≤ S)
    (huexp : (u : ℝ) = Real.exp V) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hinterval : ∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * S ^ 100)
    (ht : (t : ℝ) ≤ S) (hsize : S ^ 99 ≤ (P.card : ℝ)) (hl : 0 < l)
    (hlbound : (l : ℝ) ≤ Real.exp (V / 200)) :
    (((sampleWords P t).filter (fun f =>
      ((u / Nat.gcd (l * ∏ i, f i) u : ℕ) : ℝ) < Real.exp (9 * V / 10))).card : ℝ) /
        (P.card : ℝ) ^ t ≤ Real.exp (-V / 20) := by
  have hS1 : 1 < S := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hmax : ∀ p ∈ P, (p : ℝ) ≤ S ^ 101 := by
    intro p hp
    calc
      (p : ℝ) ≤ 2 * S ^ 100 := (hinterval p hp).2
      _ ≤ S * S ^ 100 := mul_le_mul_of_nonneg_right hS (by positivity)
      _ = S ^ 101 := by rw [pow_succ]; ring
  have hmin : ∀ p ∈ P, 3 ≤ p := by
    intro p hp
    have hpow : (4 : ℝ) ≤ S ^ 100 := by
      calc
        4 = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ S ^ 2 := pow_le_pow_left₀ (by norm_num) hS 2
        _ ≤ S ^ 100 := pow_le_pow_right₀ hS1.le (by norm_num)
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by linarith [(hinterval p hp).1]
    exact_mod_cast hpR
  have huR : 0 < (u : ℝ) := by rw [huexp]; exact Real.exp_pos _
  have hu : 0 < u := by exact_mod_cast huR
  have hlog3 : 1 ≤ Real.log 3 := by
    have h := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
    simpa only [Real.log_exp] using h
  have hpop := prime_divisor_population_log_le P u 3 hu (by norm_num) hprime hmin
  have hhits : ((P.filter (fun p => p ∣ u)).card : ℝ) ≤ S := by
    rw [huexp, Real.log_exp] at hpop
    exact hpop.trans ((div_le_self hV hlog3).trans hVS)
  exact small_reduced_modulus_probability_le P t u l S V hP hS1 hV huexp
    hprime hmax ht hhits hsize hl hlbound

/-- The random-gcd bound with exactly the prime sampling scale used in the manuscript.
No asymptotic number-theory result is hidden: existence and cardinality of the prime set
are explicit hypotheses, while the entire exceptional-event estimate is proved. -/
theorem random_gcd_exception_bound_wide (P : Finset ℕ) (t u l : ℕ) (S V : ℝ)
    (hP : P.Nonempty) (hS : 2 ≤ S) (hV : 0 ≤ V) (hVS : V ≤ S)
    (huexp : (u : ℝ) = Real.exp V) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hinterval : ∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101)
    (ht : (t : ℝ) ≤ S) (hsize : S ^ 99 ≤ (P.card : ℝ)) (hl : 0 < l)
    (hlbound : (l : ℝ) ≤ Real.exp (V / 200)) :
    (((sampleWords P t).filter (fun f =>
      ((u / Nat.gcd (l * ∏ i, f i) u : ℕ) : ℝ) < Real.exp (9 * V / 10))).card : ℝ) /
        (P.card : ℝ) ^ t ≤ Real.exp (-V / 20) := by
  have hS1 : 1 < S := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hmax : ∀ p ∈ P, (p : ℝ) ≤ S ^ 101 := fun p hp => (hinterval p hp).2
  have hmin : ∀ p ∈ P, 3 ≤ p := by
    intro p hp
    have hpow : (4 : ℝ) ≤ S ^ 100 := by
      calc
        4 = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ S ^ 2 := pow_le_pow_left₀ (by norm_num) hS 2
        _ ≤ S ^ 100 := pow_le_pow_right₀ hS1.le (by norm_num)
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by linarith [(hinterval p hp).1]
    exact_mod_cast hpR
  have huR : 0 < (u : ℝ) := by rw [huexp]; exact Real.exp_pos _
  have hu : 0 < u := by exact_mod_cast huR
  have hlog3 : 1 ≤ Real.log 3 := by
    have h := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
    simpa only [Real.log_exp] using h
  have hpop := prime_divisor_population_log_le P u 3 hu (by norm_num) hprime hmin
  have hhits : ((P.filter (fun p => p ∣ u)).card : ℝ) ≤ S := by
    rw [huexp, Real.log_exp] at hpop
    exact hpop.trans ((div_le_self hV hlog3).trans hVS)
  exact small_reduced_modulus_probability_le P t u l S V hP hS1 hV huexp
    hprime hmax ht hhits hsize hl hlbound

end Problem337.RandomProducts

end OAI
