import OAI.NumberTheory.TotientAsymptotic.SquareDivisor
import OAI.NumberTheory.TotientAsymptotic.ShiftDivisorMass

namespace OAI

/-!
The large-square-in-a-totient branch of the PPT pruning argument.
Euler's product formula reduces it to a square in the integer, a square
in one prime predecessor, or a common factor of two distinct prime
predecessors.  Elementary reciprocal divisor bounds suffice when the
cutoff is a sufficiently large fixed power of the logarithm.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

theorem ppt_totient_square_cases {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hsq : p^2 ∣ n.totient) :
    p^2 ∣ n ∨
      (∃ q : ℕ, q.Prime ∧ q ∣ n ∧ p^2 ∣ q-1) ∨
      (∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q ≠ r ∧ q ∣ n ∧ r ∣ n ∧
        p ∣ q-1 ∧ p ∣ r-1) := by
  by_cases hpn : p^2 ∣ n
  · exact Or.inl hpn
  have hnot : ¬p ∣ n/(∏ q ∈ n.primeFactors, q) := by
    intro hd
    have hrad := Nat.prod_primeFactors_dvd n
    have hpd : p ∣ n := hd.trans (Nat.div_dvd_of_dvd hrad)
    have hpmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hn.ne'⟩
    have hpRad : p ∣ ∏ q ∈ n.primeFactors, q := Finset.dvd_prod_of_mem id hpmem
    have hmul := Nat.mul_dvd_mul hpRad hd
    rw [Nat.mul_div_cancel' hrad] at hmul
    exact hpn (by simpa only [pow_two] using hmul)
  rw [Nat.totient_eq_div_primeFactors_mul] at hsq
  have hprod := hp.prime.pow_dvd_of_dvd_mul_left 2 hnot hsq
  rcases square_dvd_product n.primeFactors (fun q : ℕ => q-1) hp hprod with
    ⟨q, hq, hsq⟩ | ⟨q, hq, r, hr, hne, hqp, hrp⟩
  · exact Or.inr (Or.inl ⟨q, Nat.prime_of_mem_primeFactors hq,
      Nat.dvd_of_mem_primeFactors hq, hsq⟩)
  · exact Or.inr (Or.inr ⟨q, r, Nat.prime_of_mem_primeFactors hq,
      Nat.prime_of_mem_primeFactors hr, hne, Nat.dvd_of_mem_primeFactors hq,
      Nat.dvd_of_mem_primeFactors hr, hqp, hrp⟩)

private def pptDivisorMultiples (N d : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter (fun n => n ≠ 0 ∧ d ∣ n)

private lemma ppt_multiples_mem {N d n : ℕ} (hn : 0 < n) (hN : n ≤ N) (hd : d ∣ n) :
    n ∈ pptDivisorMultiples N d :=
  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hn.ne', hd⟩

private lemma ppt_multiples_card (N d : ℕ) :
    ((pptDivisorMultiples N d).card : ℝ) ≤ (N : ℝ)/d := by
  have he : (pptDivisorMultiples N d).card = N/d := Nat.card_multiples' N d
  rw [he]
  exact Nat.cast_div_le

private lemma ppt_shift_prime_mem {N d q : ℕ} (hq : q ∈ shiftDivisiblePrimes N d) :
    q.Prime ∧ q ≤ N ∧ d ∣ q-1 := by
  have hh := Finset.mem_filter.mp hq
  have hp := Nat.mem_primesLE.mp hh.1
  exact ⟨hp.2, hp.1, hh.2⟩

private lemma ppt_shift_prime_reciprocal (N : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ q ∈ shiftDivisiblePrimes N d, (q : ℝ)⁻¹) ≤ (1+Real.log N)/(d : ℝ) := by
  apply le_trans _ (shifted_divisor_mass N hd)
  apply Finset.sum_le_sum
  intro q hq
  have hp := (ppt_shift_prime_mem hq).1
  exact inv_anti₀ (by exact_mod_cast Nat.sub_pos_of_lt hp.one_lt)
    (Nat.cast_le.mpr (Nat.sub_le q 1))

/-- A fixed prime-square divisor of a totient is rare among all integers,
without any restriction on their total number of prime factors. -/
theorem ppt_fixed_totient_square_count {N p : ℕ} (hp : p.Prime)
    (Q : Finset ℕ) (hQ : ∀ n ∈ Q, 0 < n ∧ n ≤ N ∧ p^2 ∣ n.totient) :
    (Q.card : ℝ) ≤ (N : ℝ)*(1+(1+Real.log N)+(1+Real.log N)^2)/(p : ℝ)^2 := by
  classical
  let L : ℝ := 1+Real.log N
  let R := shiftDivisiblePrimes N (p^2)
  let S := shiftDivisiblePrimes N p
  let Q₀ := pptDivisorMultiples N (p^2)
  let Q₁ := R.biUnion (pptDivisorMultiples N)
  let F : ℕ × ℕ → Finset ℕ := fun r =>
    if r.1 = r.2 then ∅ else pptDivisorMultiples N (r.1*r.2)
  let Q₂ := (S.product S).biUnion F
  have hsub : Q ⊆ Q₀ ∪ Q₁ ∪ Q₂ := by
    intro n hn
    obtain ⟨hn0, hnN, hsq⟩ := hQ n hn
    rcases ppt_totient_square_cases hn0 hp hsq with hnSq | hOne | hTwo
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (ppt_multiples_mem hn0 hnN hnSq))
    · obtain ⟨q, hq, hqn, hqSq⟩ := hOne
      have hqR : q ∈ R := Finset.mem_filter.mpr
        ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hn0 hqn).trans hnN, hq⟩, hqSq⟩
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨q, hqR, ppt_multiples_mem hn0 hnN hqn⟩))
    · obtain ⟨q, r, hq, hr, hne, hqn, hrn, hqp, hrp⟩ := hTwo
      have hqS : q ∈ S := Finset.mem_filter.mpr
        ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hn0 hqn).trans hnN, hq⟩, hqp⟩
      have hrS : r ∈ S := Finset.mem_filter.mpr
        ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hn0 hrn).trans hnN, hr⟩, hrp⟩
      have hqrn := ((Nat.coprime_primes hq hr).mpr hne).mul_dvd_of_dvd_of_dvd hqn hrn
      apply Finset.mem_union_right
      refine Finset.mem_biUnion.mpr ⟨(q, r), Finset.mem_product.mpr ⟨hqS, hrS⟩, ?_⟩
      simpa only [F, ite_eq_right hne] using ppt_multiples_mem hn0 hnN hqrn
  have h₀ : (Q₀.card : ℝ) ≤ (N : ℝ)/(p : ℝ)^2 := by
    change ((pptDivisorMultiples N (p^2)).card : ℝ) ≤ (N : ℝ)/(p : ℝ)^2
    rw [← (Nat.cast_pow p 2 : ((p^2 : ℕ) : ℝ) = (p : ℝ)^2)]
    exact ppt_multiples_card N (p^2)
  have hR : (∑ q ∈ R, (q : ℝ)⁻¹) ≤ L/(p : ℝ)^2 := by
    simpa only [Nat.cast_pow] using ppt_shift_prime_reciprocal N (pow_pos hp.pos 2)
  have hS : (∑ q ∈ S, (q : ℝ)⁻¹) ≤ L/(p : ℝ) := ppt_shift_prime_reciprocal N hp.pos
  have h₁ : (Q₁.card : ℝ) ≤ (N : ℝ)*L/(p : ℝ)^2 := by
    calc
      _ ≤ ∑ q ∈ R, ((pptDivisorMultiples N q).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le : Q₁.card ≤ ∑ q ∈ R, (pptDivisorMultiples N q).card)
      _ ≤ ∑ q ∈ R, (N : ℝ)/q := Finset.sum_le_sum (fun q _ => ppt_multiples_card N q)
      _ = (N : ℝ)*(∑ q ∈ R, (q : ℝ)⁻¹) := by
        rw [Finset.mul_sum]
        simp only [div_eq_mul_inv]
      _ ≤ (N : ℝ)*(L/(p : ℝ)^2) := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg N)
      _ = _ := by ring
  have h₂ : (Q₂.card : ℝ) ≤ (N : ℝ)*(L/(p : ℝ))^2 := by
    calc
      _ ≤ ∑ r ∈ S.product S, ((F r).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le : Q₂.card ≤ ∑ r ∈ S.product S, (F r).card)
      _ ≤ ∑ r ∈ S.product S, (N : ℝ)/(r.1*r.2 : ℕ) := by
        apply Finset.sum_le_sum
        intro r _
        by_cases he : r.1 = r.2
        · simp only [F, ite_eq_left he, Finset.card_empty, Nat.cast_zero]
          positivity
        · simpa only [F, ite_eq_right he] using ppt_multiples_card N (r.1*r.2)
      _ = (N : ℝ)*(∑ q ∈ S, (q : ℝ)⁻¹)^2 := by
        calc
          _ = ∑ q ∈ S, ∑ r ∈ S, (N : ℝ)/((q*r : ℕ) : ℝ) :=
            Finset.sum_product S S _
          _ = _ := by
            rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q hq
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r hr
            simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hS 2)
        (Nat.cast_nonneg N)
  have hcard : (Q.card : ℝ) ≤ (Q₀.card : ℝ)+(Q₁.card : ℝ)+(Q₂.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans
      ((Finset.card_union_le (Q₀ ∪ Q₁) Q₂).trans
        (Nat.add_le_add_right (Finset.card_union_le Q₀ Q₁) Q₂.card))
  calc
    _ ≤ (N : ℝ)/(p : ℝ)^2 + (N : ℝ)*L/(p : ℝ)^2 + (N : ℝ)*(L/(p : ℝ))^2 :=
      hcard.trans (add_le_add (add_le_add h₀ h₁) h₂)
    _ = _ := by dsimp only [L]; ring

/-- Summing over the large square divisor uses the already proved inverse
square tail; the resulting cutoff may be any positive integer. -/
theorem ppt_large_totient_square_count {N K : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K)
    (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ n ≤ N ∧ ∃ p : ℕ, p.Prime ∧ K < p ∧ p^2 ∣ n.totient) :
    (Q.card : ℝ) ≤ 6*(N : ℝ)*(1+Real.log N)^2/(K : ℝ) := by
  classical
  let R := (Nat.primesLE N).filter (fun p => K < p)
  let F : ℕ → Finset ℕ := fun p => Q.filter (fun n => p^2 ∣ n.totient)
  let L : ℝ := 1+Real.log N
  have hL : 1 ≤ L := by
    dsimp only [L]
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)]
  have hsub : Q ⊆ R.biUnion F := by
    intro n hn
    obtain ⟨hn0, hnN, p, hp, hKp, hsq⟩ := hQ n hn
    have hpn : p ≤ N :=
      (Nat.le_of_dvd (Nat.totient_pos.mpr hn0)
        ((dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hsq)).trans
        ((Nat.totient_le n).trans hnN)
    exact Finset.mem_biUnion.mpr ⟨p,
      Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpn, hp⟩, hKp⟩,
      Finset.mem_filter.mpr ⟨hn, hsq⟩⟩
  have htail : (∑ p ∈ R, ((p : ℝ)^2)⁻¹) ≤ 2/(K : ℝ) := by
    apply inverse_square_tail R (by exact_mod_cast hK)
    intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2
  have hcoef : 0 ≤ (N : ℝ)*(1+L+L^2) := by positivity
  calc
    _ ≤ ∑ p ∈ R, ((F p).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ p ∈ R, (N : ℝ)*(1+L+L^2)/(p : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro p hp
      apply ppt_fixed_totient_square_count (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
      intro n hn
      have hh := Finset.mem_filter.mp hn
      exact ⟨(hQ n hh.1).1, (hQ n hh.1).2.1, hh.2⟩
    _ = (N : ℝ)*(1+L+L^2)*(∑ p ∈ R, ((p : ℝ)^2)⁻¹) := by
      rw [Finset.mul_sum]
      simp only [div_eq_mul_inv]
    _ ≤ (N : ℝ)*(1+L+L^2)*(2/(K : ℝ)) := mul_le_mul_of_nonneg_left htail hcoef
    _ ≤ _ := by
      have hpoly : 1+L+L^2 ≤ 3*L^2 := by nlinarith
      have hh := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ (N : ℝ) by positivity)
      have hdiv := mul_le_mul_of_nonneg_right hh (show 0 ≤ 2/(K : ℝ) by positivity)
      dsimp only [L] at hdiv ⊢
      exact hdiv.trans_eq (by ring)

end TotientAsymptotic

end

end OAI
