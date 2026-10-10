import OAI.NumberTheory.ShortEgyptian.MomentAsymptotics

namespace OAI

namespace ShortEgyptian

open Finset
def dyadicPrimes (n : ℕ) : Finset ℕ := (Ioc n (2*n)).filter Nat.Prime

theorem centralBinom_le_with_prime_count (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤ (2*n)^Nat.sqrt (2*n)*4^(2*n/3)*(2*n)^(dyadicPrimes n).card := by
  classical
  let f p := p ^ n.centralBinom.factorization p
  let A := Nat.primesLE (2*n/3)
  let B := dyadicPrimes n
  have hpos : 0 < n := by omega
  have htwo : 1 ≤ 2*n := by omega
  have hdis : Disjoint A B := by
    rw [disjoint_left]
    intro p hpA hpB
    have hpa := (Nat.mem_primesLE.mp hpA).1
    have hpb := (mem_Ioc.mp (mem_filter.mp hpB).1).1
    have : 2*n/3 ≤ n := by omega
    omega
  have hab : n.centralBinom = (∏ p ∈ A, f p)*(∏ p ∈ B, f p) := by
    rw [← prod_union hdis]
    rw [← n.prod_pow_factorization_centralBinom]
    symm
    apply prod_subset
    · intro p hp
      rcases mem_union.mp hp with hp | hp
      · have hh := (Nat.mem_primesLE.mp hp).1
        exact mem_range.mpr (by omega)
      · exact mem_range.mpr (by have hh := (mem_Ioc.mp (mem_filter.mp hp).1).2; omega)
    · intro p hp hpnot
      dsimp [f]
      by_cases hprime : p.Prime
      · have hplow : 2*n/3 < p := by
          by_contra! h
          exact hpnot (mem_union.mpr (Or.inl (Nat.mem_primesLE.mpr ⟨h,hprime⟩)))
        have hpn : p ≤ n := by
          by_contra! h
          exact hpnot (mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_Ioc.mpr ⟨h,by have hh := mem_range.mp hp; omega⟩,hprime⟩)))
        have hthree : 2*n < 3*p := by omega
        rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpn hthree,pow_zero]
      · rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom hprime,pow_zero]
  have hlow : (∏ p ∈ A, f p) ≤ (2*n)^Nat.sqrt (2*n)*4^(2*n/3) := by
    rw [← prod_filter_mul_prod_filter_not A (fun p => p ≤ Nat.sqrt (2*n))]
    apply mul_le_mul'
    · apply (prod_le_prod (fun p _ => (show f p ≤ 2*n from Nat.pow_factorization_choose_le (by omega)))).trans
      rw [prod_const]
      apply Nat.pow_le_pow_right htwo
      apply (card_le_card (show A.filter (fun p => p ≤ Nat.sqrt (2*n)) ⊆ Icc 1 (Nat.sqrt (2*n)) from ?_)).trans
      · rw [Nat.card_Icc,Nat.add_sub_cancel]
      · intro p hp
        exact mem_Icc.mpr ⟨(Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.one_lt.le,(mem_filter.mp hp).2⟩
    · apply le_trans _ (primorial_le_four_pow (2*n/3))
      have hp : ∀ p ∈ A.filter (fun p => ¬p ≤ Nat.sqrt (2*n)), f p ≤ p := by
        intro p hp
        have hprime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
        have hlarge := (mem_filter.mp hp).2
        have hf : n.centralBinom.factorization p ≤ 1 := Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp (not_le.mp hlarge))
        exact (Nat.pow_le_pow_right hprime.one_lt.le hf).trans_eq (pow_one p)
      apply (prod_le_prod hp).trans
      change (∏ p ∈ A.filter (fun p => ¬p ≤ Nat.sqrt (2*n)), p) ≤ ∏ p ∈ A, p
      exact prod_le_prod_of_subset_of_one_le (filter_subset _ _) (fun p hp _ => (Nat.mem_primesLE.mp hp).2.one_lt.le)
  have hhigh : (∏ p ∈ B, f p) ≤ (2*n)^B.card := by
    calc
      _ ≤ ∏ _p ∈ B, 2*n := prod_le_prod (fun p _ => Nat.pow_factorization_choose_le (by omega))
      _ = _ := prod_const _
  rw [hab]
  exact mul_le_mul' hlow hhigh

theorem dyadic_prime_log_lower (n : ℕ) (hn : 4 ≤ n) :
    (n:ℝ)/3*Real.log 4 ≤ Real.log n + Real.sqrt (2*(n:ℝ))*Real.log (2*(n:ℝ)) +
      ((dyadicPrimes n).card:ℝ)*Real.log (2*(n:ℝ)) := by
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hbin : (0:ℝ) < n.centralBinom := by exact_mod_cast n.centralBinom_pos
  have hlow := Real.log_le_log (by positivity : (0:ℝ)<(4:ℝ)^n)
    (show (4:ℝ)^n ≤ (n:ℝ)*n.centralBinom by exact_mod_cast (Nat.four_pow_lt_mul_centralBinom n hn).le)
  rw [Real.log_pow,Real.log_mul hnR.ne' hbin.ne'] at hlow
  have hup := Real.log_le_log hbin (show (n.centralBinom:ℝ) ≤
    (2*(n:ℝ))^Nat.sqrt (2*n)*4^(2*n/3)*(2*(n:ℝ))^(dyadicPrimes n).card by
      exact_mod_cast centralBinom_le_with_prime_count n (by omega))
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow,Real.log_pow] at hup
  have hsqrt : (Nat.sqrt (2*n):ℝ) ≤ Real.sqrt (2*(n:ℝ)) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (Real.nat_sqrt_le_real_sqrt (a := 2*n))
  have hdiv : (↑(2*n/3):ℝ) ≤ 2*(n:ℝ)/3 := by
    exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := 2*n) (n := 3))
  have hlog2n : 0 ≤ Real.log (2*(n:ℝ)) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2*n))
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h1 := mul_le_mul_of_nonneg_right hsqrt hlog2n
  have h2 := mul_le_mul_of_nonneg_right hdiv hlog4
  linarith

theorem dyadic_prime_count_lower (n : ℕ) (hn : 4 ≤ n) (hl : 1 ≤ Real.log n)
    (hsmall : 30*Real.log n ≤ Real.sqrt n) :
    (n:ℝ)/(20*Real.log n) ≤ ((dyadicPrimes n).card:ℝ) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1≤n)
  have hl0 : 0 < Real.log n := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hlog4 : (1:ℝ) ≤ Real.log 4 := by
    have hh : Real.log (4:ℝ) = 2*Real.log 2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
    rw [hh]; linarith [Real.log_two_gt_d9]
  have hlog2n : Real.log (2*(n:ℝ)) ≤ 2*Real.log n := by
    rw [Real.log_mul (by norm_num) hn0.ne']; linarith
  have hsqrt : Real.sqrt (2*(n:ℝ)) ≤ 2*Real.sqrt n := by
    have hsq := Real.sq_sqrt hn0.le
    have hsq2 := Real.sq_sqrt (show 0≤2*(n:ℝ) by positivity)
    nlinarith [Real.sqrt_nonneg (n:ℝ),Real.sqrt_nonneg (2*(n:ℝ))]
  have hsqrt1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
  have herror : Real.log n + Real.sqrt (2*(n:ℝ))*Real.log (2*(n:ℝ)) ≤ (n:ℝ)/6 := by
    have h1 := mul_le_mul hsqrt hlog2n (Real.log_nonneg (by linarith : 1≤2*(n:ℝ))) (by positivity : 0≤2*Real.sqrt n)
    have h2 := mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg (n:ℝ))
    have h3 := Real.sq_sqrt hn0.le
    nlinarith only [h1,h2,h3,hsqrt1,hl0]
  have hmain := dyadic_prime_log_lower n hn
  have hlogterm := mul_le_mul_of_nonneg_left hlog2n (Nat.cast_nonneg (dyadicPrimes n).card)
  have hlower := mul_le_mul_of_nonneg_left hlog4 (by positivity : 0 ≤ (n:ℝ)/3)
  apply (div_le_iff₀ (by positivity : 0 < 20*Real.log n)).mpr
  nlinarith only [hmain,hlogterm,hlower,herror,hn0]

noncomputable def scalePrimes (S : ℝ) : Finset ℕ := dyadicPrimes ⌊S^100⌋₊

lemma scalePrimes_mem (S : ℝ) (p : ℕ) (hp : p ∈ scalePrimes S) :
    p.Prime ∧ S^100 ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*S^100 := by
  obtain ⟨hI,hprime⟩ := mem_filter.mp hp
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hI
  have hS : 0 ≤ S^100 := even_two.mul_right (50:ℕ) |>.pow_nonneg S
  refine ⟨hprime,?_,?_⟩
  · exact (Nat.lt_of_floor_lt hlo).le
  · have hh : (p:ℝ) ≤ 2*(⌊S^100⌋₊:ℝ) := by exact_mod_cast hhi
    exact hh.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hS) (by norm_num))

lemma scalePrimes_card (S : ℝ) (hS : 2 ≤ S) (hlog : 1 ≤ Real.log S)
    (hbig : 4000*Real.log S ≤ S) : S^99 ≤ ((scalePrimes S).card:ℝ) := by
  let n := ⌊S^100⌋₊
  have hS0 : 0 < S := by linarith
  have hnU : (n:ℝ) ≤ S^100 := Nat.floor_le (by positivity)
  have hnL : S^100-1 < (n:ℝ) := Nat.sub_one_lt_floor _
  have hpow : S^4 ≤ S^100 := pow_le_pow_right₀ (by linarith) (by norm_num : 4 ≤ 100)
  have hsq : 4 ≤ S^2 := by nlinarith
  have hnBig : S^2 ≤ (n:ℝ) := by nlinarith [sq_nonneg (S^2-2)]
  have hn4 : 4 ≤ n := by exact_mod_cast (hsq.trans hnBig)
  have hn0 : 0 < (n:ℝ) := by linarith
  have hnl : 1 ≤ Real.log n := by
    have hh := Real.log_le_log (sq_pos_of_pos hS0) hnBig
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hnlog : Real.log n ≤ 100*Real.log S := by
    have hh := Real.log_le_log hn0 hnU
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hroot : S ≤ Real.sqrt n := by
    exact (Real.le_sqrt hS0.le (Nat.cast_nonneg n)).mpr hnBig
  have herr : 30*Real.log n ≤ Real.sqrt n := by linarith
  have hh := dyadic_prime_count_lower n hn4 hnl herr
  apply le_trans _ hh
  apply (le_div_iff₀ (by positivity : 0 < 20*Real.log n)).mpr
  have hhalf : S^100/2 ≤ (n:ℝ) := by
    have h100 : 2 ≤ S^100 := by linarith
    linarith
  calc
    _ ≤ S^99*(2000*Real.log S) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ S^99*(S/2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = S^100/2 := by ring
    _ ≤ _ := hhalf

end ShortEgyptian

end OAI
