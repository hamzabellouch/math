import OAI.NumberTheory.TotientAsymptotic.OmegaReciprocal
import OAI.NumberTheory.TotientAsymptotic.SuffixFactorization

namespace OAI

/-! Prime-factor counts in actual residual totients, including a repeated
last prime in the cofactor. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma omega_count_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a*b).primeFactorsList.length=a.primeFactorsList.length+b.primeFactorsList.length := by
  simpa only [List.length_append] using (Nat.perm_primeFactorsList_mul ha hb).length_eq

lemma omega_count_prod {ι : Type*} (I : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ I, f i ≠ 0) :
    (∏ i ∈ I, f i).primeFactorsList.length=∑ i ∈ I, (f i).primeFactorsList.length := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi,omega_count_mul
      (hf i (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma omega_count_le_log {n : ℕ} (hn : 0 < n) :
    (n.primeFactorsList.length : ℝ) ≤ 2*Real.log n := by
  have hnat : (2 : ℕ)^n.primeFactorsList.length ≤ n := by
    calc
      _ ≤ n.primeFactorsList.prod := List.pow_length_le_prod _ 2
        (fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)
      _ = n := Nat.prod_primeFactorsList hn.ne'
  have hp : (2 : ℝ)^n.primeFactorsList.length ≤ n := by exact_mod_cast hnat
  have hh := Real.log_le_log (by positivity : (0 : ℝ)<2^n.primeFactorsList.length) hp
  rw [Real.log_pow] at hh
  have hl : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg n.primeFactorsList.length : (0 : ℝ) ≤ n.primeFactorsList.length)]

lemma totient_prime_factor_count {a p : ℕ} (ha : 0 < a) (hp : p.Prime) :
    (a*p).totient.primeFactorsList.length ≤
      a.totient.primeFactorsList.length+(p-1).primeFactorsList.length+1 := by
  rw [Nat.mul_comm a p]
  by_cases hd : p ∣ a
  · rw [Nat.totient_mul_of_prime_of_dvd hp hd,
      omega_count_mul hp.ne_zero (Nat.totient_pos.mpr ha).ne',Nat.primeFactorsList_prime hp]
    simp only [List.length_singleton]
    omega
  · rw [Nat.totient_mul_of_prime_of_not_dvd hp hd,
      omega_count_mul (by have := hp.two_le; omega) (Nat.totient_pos.mpr ha).ne']
    omega

/-- Only one extra occurrence is paid for possible overlap at the last
prime; every other shifted-prime factor is exact. -/
lemma basic_suffix_factor_count {x : ℝ} {H k : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hL : L x H < m x) (hk : k < L x H) :
    ((suffixPreimage η k).totient.primeFactorsList.length : ℝ) ≤
      2*Real.log (η.cofactor : ℝ)+1+
        ∑ j ∈ Finset.Icc (k+1) (L x H), ((remainderPrime η j-1).primeFactorsList.length : ℝ) := by
  have hLpos : 0 < L x H := by omega
  have hlast := (hη.2.1 (L x H) (Finset.mem_Icc.mpr ⟨hLpos,le_rfl⟩)).1
  have he : suffixPreimage η (L x H-1)=η.cofactor*remainderPrime η (L x H) := by
    simp only [suffixPreimage,Nat.sub_add_cancel hLpos,Finset.Icc_self,Finset.prod_singleton]
  have hz (j : ℕ) (hj : j ∈ Finset.Icc (k+1) (L x H-1)) : remainderPrime η j-1 ≠ 0 := by
    have hprime := (hη.2.1 j (Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Icc.mp hj).1; omega,by have := (Finset.mem_Icc.mp hj).2; omega⟩)).1
    have := hprime.two_le
    omega
  have hsplit := basic_suffix_totient_split hη hL (by omega : k ≤ L x H-1) (by omega : L x H-1 < L x H)
  have hbase := totient_prime_factor_count hη.1 hlast
  have hadd : (suffixPreimage η k).totient.primeFactorsList.length =
      (η.cofactor*remainderPrime η (L x H)).totient.primeFactorsList.length+
        ∑ j ∈ Finset.Icc (k+1) (L x H-1), (remainderPrime η j-1).primeFactorsList.length := by
    rw [hsplit,he,omega_count_mul (Nat.totient_pos.mpr (Nat.mul_pos hη.1 hlast.pos)).ne'
      (Finset.prod_ne_zero_iff.mpr hz),omega_count_prod _ _ hz]
  have hsum : (∑ j ∈ Finset.Icc (k+1) (L x H), (remainderPrime η j-1).primeFactorsList.length) =
      (∑ j ∈ Finset.Icc (k+1) (L x H-1), (remainderPrime η j-1).primeFactorsList.length)+
        (remainderPrime η (L x H)-1).primeFactorsList.length := by
    have hI : Finset.Icc (k+1) (L x H) = insert (L x H) (Finset.Icc (k+1) (L x H-1)) := by
      ext j
      simp only [Finset.mem_Icc,Finset.mem_insert]
      omega
    rw [hI,Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    omega

  have hnat : (suffixPreimage η k).totient.primeFactorsList.length ≤
      η.cofactor.totient.primeFactorsList.length+1+
        ∑ j ∈ Finset.Icc (k+1) (L x H), (remainderPrime η j-1).primeFactorsList.length := by
    rw [hadd,hsum]
    omega
  have hcof : (η.cofactor.totient.primeFactorsList.length : ℝ) ≤ 2*Real.log (η.cofactor : ℝ) :=
    (omega_count_le_log (Nat.totient_pos.mpr hη.1)).trans
      (mul_le_mul_of_nonneg_left (Real.log_le_log (by exact_mod_cast Nat.totient_pos.mpr hη.1)
        (by exact_mod_cast Nat.totient_le η.cofactor)) (by norm_num))
  have hnatR : ((suffixPreimage η k).totient.primeFactorsList.length : ℝ) ≤
      (η.cofactor.totient.primeFactorsList.length : ℝ)+1+
        ∑ j ∈ Finset.Icc (k+1) (L x H), ((remainderPrime η j-1).primeFactorsList.length : ℝ) := by exact_mod_cast hnat
  linarith

end TotientAsymptotic

end

end OAI
