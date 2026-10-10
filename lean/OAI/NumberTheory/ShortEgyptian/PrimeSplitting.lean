import OAI.NumberTheory.ShortEgyptian.TruncatedDivisors

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem small_prime_divisor_bound {n : ℕ} (hn : n ≠ 0) (z W : ℝ)
    (hz : 0 ≤ z) (hW : Real.log n ≤ W)
    (hsmooth : ∀ p ∈ n.primeFactorsList, (p:ℝ) ≤ z) :
    (n.divisors.card : ℝ) ≤ Real.exp (z * Real.log (1+W/Real.log 2)) := by
  classical
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hΩ : (ArithmeticFunction.cardFactors n : ℝ) ≤ W / Real.log 2 := by
    apply (le_div_iff₀ hl2).mpr
    exact (rough_cardFactors_log hn 2 (by norm_num) (fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactorsList hp).two_le)).trans hW
  have hΩ0 : 0 ≤ W/Real.log 2 := le_trans (Nat.cast_nonneg _) hΩ
  have hfac (p : ℕ) : n.factorization p ≤ ArithmeticFunction.cardFactors n := by
    rw [ArithmeticFunction.cardFactors_eq_sum_factorization]
    simpa using (Finsupp.single_le_sum n.factorization (g := fun _ k => k) (fun _ k => Nat.zero_le k) p)
  have hcard : (n.primeFactors.card:ℝ) ≤ z := by
    have hsub : n.primeFactors ⊆ Icc 1 ⌊z⌋₊ := by
      intro p hp
      have hh := Nat.mem_primeFactors.mp hp
      exact mem_Icc.mpr ⟨hh.1.one_lt.le, Nat.le_floor (hsmooth p ((Nat.mem_primeFactorsList hn).mpr ⟨hh.1,hh.2.1⟩))⟩
    have hhh := card_le_card hsub
    have hc : n.primeFactors.card ≤ ⌊z⌋₊ := by simpa using hhh
    exact le_trans (by exact_mod_cast hc) (Nat.floor_le hz)
  calc
    _ = ∏ p ∈ n.primeFactors, ((n.factorization p:ℝ)+1) := by rw [Nat.card_divisors hn, Nat.cast_prod]; simp
    _ ≤ (1+W/Real.log 2)^n.primeFactors.card := by
      calc
        _ ≤ ∏ _p ∈ n.primeFactors, (1+W/Real.log 2) := by
          apply prod_le_prod₀ (fun p _ => by positivity)
          intro p _
          have hh : (n.factorization p:ℝ) ≤ ArithmeticFunction.cardFactors n := by exact_mod_cast hfac p
          linarith
        _ = _ := by simp
    _ = Real.exp ((n.primeFactors.card:ℝ)*Real.log (1+W/Real.log 2)) := by
      rw [Real.exp_nat_mul,Real.exp_log (by linarith)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hcard (Real.log_nonneg (by linarith))

theorem prime_threshold_split {n : ℕ} (hn : n ≠ 0) (z : ℝ) :
    ∃ d e : ℕ, n = d*e ∧ d ≠ 0 ∧ e ≠ 0 ∧
      (∀ p ∈ d.primeFactorsList, (p:ℝ) ≤ z) ∧
      (∀ p ∈ e.primeFactorsList, z ≤ p) := by
  classical
  let l := n.primeFactorsList
  let f (p : ℕ) : Bool := decide ((p:ℝ) < z)
  let d := (l.filter f).prod
  let e := (l.filter (fun p => !f p)).prod
  have hde : n = d*e := by
    have hh := (List.filter_append_perm f l).prod_eq
    rw [List.prod_append, Nat.prod_primeFactorsList hn] at hh
    exact hh.symm
  have hd : d ≠ 0 := by intro hh; simp [hh] at hde; exact hn hde
  have he : e ≠ 0 := by intro hh; simp [hh] at hde; exact hn hde
  refine ⟨d,e,hde,hd,he,?_,?_⟩
  · intro p hp
    have hh := mem_list_primes_of_dvd_prod (Nat.prime_of_mem_primeFactorsList hp).prime
      (L := l.filter f) (fun q hq => (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime)
      (Nat.dvd_of_mem_primeFactorsList hp)
    have hlt : (p:ℝ) < z := by simpa [f] using (List.mem_filter.mp hh).2
    exact hlt.le
  · intro p hp
    have hh := mem_list_primes_of_dvd_prod (Nat.prime_of_mem_primeFactorsList hp).prime
      (L := l.filter (fun q => !f q)) (fun q hq => (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime)
      (Nat.dvd_of_mem_primeFactorsList hp)
    have hlt : ¬ (p:ℝ) < z := by simpa [f] using (List.mem_filter.mp hh).2
    exact le_of_not_gt hlt

theorem truncated_pointwise_bound {n : ℕ} (hn : n ≠ 0) (X W z q : ℝ)
    (hz : 1 < z) (hq0 : 0 < q) (hq1 : q < 1) (hW : Real.log n ≤ W) :
    (truncatedDivisorCount X n:ℝ) ≤ Real.exp
      (z * Real.log (1+W/Real.log 2) + (q*W-Real.log X*Real.log q)/Real.log z) := by
  obtain ⟨d,e,hde,hd,he,hs,hr⟩ := prime_threshold_split hn z
  have hdle : (d:ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (hde ▸ dvd_mul_right d e)
  have hele : (e:ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (hde ▸ dvd_mul_left e d)
  have hdW := (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hd) hdle).trans hW
  have heW := (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero he) hele).trans hW
  have hm : (truncatedDivisorCount X n:ℝ) ≤ (d.divisors.card:ℝ)*truncatedDivisorCount X e := by
    exact_mod_cast (hde ▸ truncatedDivisors_mul X hd he)
  calc
    _ ≤ _ := hm
    _ ≤ Real.exp (z * Real.log (1+W/Real.log 2)) *
          Real.exp ((q*W-Real.log X*Real.log q)/Real.log z) :=
      mul_le_mul (small_prime_divisor_bound hd z W (by linarith) hdW hs)
        (rough_truncated_bound he X W z q hz hq0 hq1 heW hr) (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

theorem prime_prefix_split {n : ℕ} (hn : n ≠ 0) (R : ℝ) (hR : 1 ≤ R) (hnR : R < n) :
    ∃ d e p : ℕ, n = d*e ∧ d ≠ 0 ∧ e ≠ 0 ∧ p.Prime ∧ p ∣ e ∧
      (d:ℝ) ≤ R ∧ R < (d:ℝ)*p ∧
      (∀ q ∈ d.primeFactorsList, q ≤ p) ∧ (∀ q ∈ e.primeFactorsList, p ≤ q) := by
  induction n using Nat.strong_induction_on generalizing R with
  | h n ih =>
    have hn1 : n ≠ 1 := by intro h; simp [h] at hnR; linarith
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime hn1
    have hp0 : 0 < (p:ℝ) := by exact_mod_cast hp.pos
    by_cases hpR : R < p
    · refine ⟨1,n,p, by simp, by norm_num, hn, hp, Nat.minFac_dvd n, ?_, ?_, ?_, ?_⟩
      · simpa using hR
      · simpa using hpR
      · simp
      · intro q hq
        exact Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactorsList hq).two_le
          (Nat.dvd_of_mem_primeFactorsList hq)
    · have hpR' : (p:ℝ) ≤ R := le_of_not_gt hpR
      let m := n/p
      have hmul : n = p*m := (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm
      have hm : m ≠ 0 := by intro h; simp [h] at hmul; exact hn hmul
      have hlt : m < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp.one_lt
      have hmR : R / p < (m:ℝ) := by
        apply (div_lt_iff₀ hp0).mpr
        have hh : (n:ℝ) = (p:ℝ)*m := by exact_mod_cast hmul
        nlinarith
      obtain ⟨d,e,q, hde, hd, he, hq, hqe, hdR, hRdp, hdq, heq⟩ :=
        ih m hlt hm (R/p) ((le_div_iff₀ hp0).mpr (by nlinarith)) hmR
      have hpq : p ≤ q := by
        apply Nat.minFac_le_of_dvd hq.two_le
        exact hqe.trans (by rw [hmul,hde]; exact dvd_mul_of_dvd_right (dvd_mul_left e d) p)
      refine ⟨p*d,e,q, ?_, mul_ne_zero hp.ne_zero hd, he, hq, hqe, ?_, ?_, ?_, heq⟩
      · rw [hmul,hde,mul_assoc]
      · have hh := (le_div_iff₀ hp0).mp hdR
        push_cast
        nlinarith
      · have hh := (div_lt_iff₀ hp0).mp hRdp
        push_cast
        nlinarith
      · intro a ha
        have hap := Nat.prime_of_mem_primeFactorsList ha
        have had := Nat.dvd_of_mem_primeFactorsList ha
        rcases hap.dvd_mul.mp had with hah | hah
        · rcases (Nat.dvd_prime hp).mp hah with h1 | h1
          · exact False.elim (hap.ne_one h1)
          · simpa [h1] using hpq
        · exact hdq a ((Nat.mem_primeFactorsList hd).mpr ⟨hap,hah⟩)

end ShortEgyptian

end OAI
