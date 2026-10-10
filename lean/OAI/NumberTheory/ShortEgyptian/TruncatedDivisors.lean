import OAI.NumberTheory.ShortEgyptian.DivisorWeights

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

noncomputable def truncatedDivisors (X : ℝ) (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun a => (a:ℝ) ≤ X

noncomputable def truncatedDivisorCount (X : ℝ) (n : ℕ) : ℕ :=
  (truncatedDivisors X n).card

theorem truncatedDivisors_mul (X : ℝ) {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    truncatedDivisorCount X (d*e) ≤ d.divisors.card * truncatedDivisorCount X e := by
  classical
  have hsub : truncatedDivisors X (d*e) ⊆
      (d.divisors ×ˢ truncatedDivisors X e).image (fun bc => bc.1 * bc.2) := by
    intro a ha
    obtain ⟨ha, hX⟩ := mem_filter.mp ha
    obtain ⟨had, han⟩ := Nat.mem_divisors.mp ha
    obtain ⟨b, c, hb, hc, hbc⟩ := exists_dvd_and_dvd_of_dvd_mul had
    have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hb (Nat.pos_of_ne_zero hd)
    have hcle : c ≤ a := by rw [hbc]; exact Nat.le_mul_of_pos_left c hbpos
    exact mem_image.mpr ⟨(b,c), mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hb,hd⟩,
      mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hc,he⟩, le_trans (by exact_mod_cast hcle) hX⟩⟩, hbc.symm⟩
  calc
    _ ≤ ((d.divisors ×ˢ truncatedDivisors X e).image (fun bc => bc.1 * bc.2)).card := card_le_card hsub
    _ ≤ (d.divisors ×ˢ truncatedDivisors X e).card := card_image_le
    _ = _ := by simp [truncatedDivisorCount]

theorem rough_cardFactors_log {n : ℕ} (hn : n ≠ 0) (z : ℝ) (hz : 0 < z)
    (hrough : ∀ p ∈ n.primeFactorsList, z ≤ p) :
    (ArithmeticFunction.cardFactors n : ℝ) * Real.log z ≤ Real.log n := by
  have hprod : (n.primeFactorsList.map (fun p : ℕ => (p:ℝ))).prod = n := by
    rw [← Nat.cast_list_prod, Nat.prod_primeFactorsList hn]
  have hlog := Real.log_list_prod (l := n.primeFactorsList.map (fun p : ℕ => (p:ℝ))) (by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact_mod_cast (Nat.pos_of_mem_primeFactorsList hp).ne')
  rw [hprod, List.map_map] at hlog
  have hh := List.length_nsmul_le_sum (n.primeFactorsList.map (fun p : ℕ => Real.log (p:ℝ))) (Real.log z) (by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact Real.log_le_log hz (hrough p hp))
  rw [hlog]
  simpa [ArithmeticFunction.cardFactors_apply, List.length_map, nsmul_eq_mul, Function.comp_def] using hh

theorem divisor_generating_prime_mul (q : ℝ) (hq : 0 ≤ q) {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0) :
    ∑ d ∈ (p*m).divisors, q^(ArithmeticFunction.cardFactors d) ≤
      (1+q) * ∑ d ∈ m.divisors, q^(ArithmeticFunction.cardFactors d) := by
  classical
  let w (d : ℕ) : ℝ := q^(ArithmeticFunction.cardFactors d)
  have hw (d : ℕ) : 0 ≤ w d := pow_nonneg hq _
  have hsub : (p*m).divisors ⊆ m.divisors ∪ m.divisors.image (p*·) := by
    intro d hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    apply mem_union.mpr
    by_cases hpd : p ∣ d
    · right
      refine mem_image.mpr ⟨d/p, Nat.mem_divisors.mpr ⟨?_, hm⟩, Nat.mul_div_cancel' hpd⟩
      have hh := Nat.div_dvd_div hpd hdvd
      simpa [Nat.mul_div_cancel_left m hp.pos] using hh
    · left
      exact Nat.mem_divisors.mpr ⟨((hp.coprime_iff_not_dvd.mpr hpd).symm).dvd_of_dvd_mul_left hdvd, hm⟩
  have hsum : (∑ d ∈ m.divisors ∪ m.divisors.image (p*·), w d) ≤
      (∑ d ∈ m.divisors, w d) + ∑ d ∈ m.divisors.image (p*·), w d := by
    have hh := sum_union_inter (s₁ := m.divisors) (s₂ := m.divisors.image (p*·)) (f := w)
    have hnn := sum_nonneg (s := m.divisors ∩ m.divisors.image (p*·)) (fun d _ => hw d)
    linarith
  calc
    _ ≤ ∑ d ∈ m.divisors ∪ m.divisors.image (p*·), w d :=
      sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hw d)
    _ ≤ _ := hsum
    _ = (∑ d ∈ m.divisors, w d) + ∑ d ∈ m.divisors, w (p*d) := by
      rw [sum_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp.pos h)]
    _ = _ := by
      have hmul : ∀ d ∈ m.divisors, w (p*d) = q * w d := by
        intro d hd
        unfold w
        rw [ArithmeticFunction.cardFactors_mul hp.ne_zero (Nat.pos_of_mem_divisors hd).ne',
          ArithmeticFunction.cardFactors_apply_prime hp, pow_add, pow_one]
      rw [sum_congr rfl hmul, ← mul_sum]
      ring

theorem divisor_generating_bound (q : ℝ) (hq : 0 ≤ q) (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, q^(ArithmeticFunction.cardFactors d) ≤
      (1+q)^(ArithmeticFunction.cardFactors n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n = 1
    · simp [hn1]
    have hp := Nat.minFac_prime hn1
    have hm : n / n.minFac ≠ 0 := by
      have hmul := Nat.mul_div_cancel' (Nat.minFac_dvd n)
      intro hz
      simp [hz] at hmul
      exact hn hmul.symm
    have hlt := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp.one_lt
    have hmul : n = n.minFac * (n / n.minFac) := (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm
    calc
      _ = ∑ d ∈ (n.minFac * (n / n.minFac)).divisors, q^(ArithmeticFunction.cardFactors d) := by
        rw [← hmul]
      _ ≤ (1+q) * ∑ d ∈ (n / n.minFac).divisors, q^(ArithmeticFunction.cardFactors d) :=
        divisor_generating_prime_mul q hq hp hm
      _ ≤ (1+q) * (1+q)^(ArithmeticFunction.cardFactors (n / n.minFac)) :=
        mul_le_mul_of_nonneg_left (ih _ hlt hm) (by linarith)
      _ = _ := by
        conv_rhs => rw [hmul]
        rw [ArithmeticFunction.cardFactors_mul hp.ne_zero hm,
          ArithmeticFunction.cardFactors_apply_prime hp, pow_add, pow_one]

theorem rough_truncated_bound {n : ℕ} (hn : n ≠ 0) (X W z q : ℝ)
    (hz : 1 < z) (hq0 : 0 < q) (hq1 : q < 1)
    (hW : Real.log n ≤ W) (hrough : ∀ p ∈ n.primeFactorsList, z ≤ p) :
    (truncatedDivisorCount X n : ℝ) ≤
      Real.exp ((q * W - Real.log X * Real.log q) / Real.log z) := by
  classical
  have hlz : 0 < Real.log z := Real.log_pos hz
  have hlq : Real.log q < 0 := Real.log_neg hq0 hq1
  have hΩ : (ArithmeticFunction.cardFactors n : ℝ) ≤ W / Real.log z := by
    apply (le_div_iff₀ hlz).mpr
    exact (rough_cardFactors_log hn z (by linarith) hrough).trans hW
  let L := Real.log q * (Real.log X / Real.log z)
  let U := q * W / Real.log z
  have hlower : (truncatedDivisorCount X n : ℝ) * Real.exp L ≤
      ∑ a ∈ truncatedDivisors X n, q^(ArithmeticFunction.cardFactors a) := by
    calc
      _ = ∑ _a ∈ truncatedDivisors X n, Real.exp L := by simp [truncatedDivisorCount]
      _ ≤ _ := by
        apply sum_le_sum
        intro a ha
        have ha' := mem_filter.mp ha
        have had := Nat.mem_divisors.mp ha'.1
        have ha0 : 0 < (a:ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors ha'.1
        have hΩa := rough_cardFactors_log (Nat.pos_of_mem_divisors ha'.1).ne' z (by linarith)
          (fun p hp => hrough p (Nat.primeFactorsList_subset_of_dvd had.1 hn hp))
        have hlog := Real.log_le_log ha0 ha'.2
        have hΩa' : (ArithmeticFunction.cardFactors a : ℝ) ≤ Real.log X / Real.log z :=
          (le_div_iff₀ hlz).mpr (hΩa.trans hlog)
        have hmul := mul_le_mul_of_nonpos_left hΩa' hlq.le
        calc
          _ ≤ Real.exp (Real.log q * (ArithmeticFunction.cardFactors a : ℝ)) := Real.exp_le_exp.mpr hmul
          _ = _ := by rw [mul_comm, Real.exp_nat_mul, Real.exp_log hq0]
  have hupper : (∑ a ∈ n.divisors, q^(ArithmeticFunction.cardFactors a)) ≤ Real.exp U := by
    calc
      _ ≤ (1+q)^(ArithmeticFunction.cardFactors n) := divisor_generating_bound q hq0.le n hn
      _ = Real.exp ((ArithmeticFunction.cardFactors n : ℝ) * Real.log (1+q)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0 < 1+q)]
      _ ≤ Real.exp ((ArithmeticFunction.cardFactors n : ℝ) * q) := by
        apply Real.exp_le_exp.mpr
        have hh := Real.log_le_sub_one_of_pos (by linarith : 0 < 1+q)
        gcongr
        linarith
      _ ≤ Real.exp U := by
        apply Real.exp_le_exp.mpr
        dsimp [U]
        calc
          _ = q * (ArithmeticFunction.cardFactors n : ℝ) := mul_comm _ _
          _ ≤ q * (W / Real.log z) := mul_le_mul_of_nonneg_left hΩ hq0.le
          _ = _ := by ring
  have hbound := hlower.trans ((sum_le_sum_of_subset_of_nonneg
    (filter_subset _ _) (fun a _ _ => pow_nonneg hq0.le (ArithmeticFunction.cardFactors a))).trans hupper)
  have heq : Real.exp ((q * W - Real.log X * Real.log q) / Real.log z) * Real.exp L = Real.exp U := by
    rw [← Real.exp_add]
    congr 1
    dsimp [L,U]
    ring
  nlinarith [Real.exp_pos L]

end ShortEgyptian

end OAI
