import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SmoothPart

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinarySmoothRough
open Finset

lemma log_smoothPart (S : Finset ℕ) (n : ℕ) :
    Real.log (smoothPart S n : ℝ) = ∑ p ∈ S, (n.factorization p : ℝ)*Real.log p := by
  classical
  rw [smoothPart, Nat.cast_prod, Real.log_prod]
  · simp only [Nat.cast_pow, Real.log_pow]
    have he : n.primeFactors.filter (fun p => p ∈ S) = n.primeFactors ∩ S := by ext p; simp
    rw [he, Finset.inter_comm]
    apply sum_subset Finset.inter_subset_left
    intro p hp hpn
    have hp' : p ∉ n.primeFactors := by intro hh; exact hpn (Finset.mem_inter.mpr ⟨hp,hh⟩)
    have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp'
    simp [hz]
  · intro p hp
    exact_mod_cast pow_ne_zero (n.factorization p)
      (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1))

lemma sum_factorization_le {p : ℕ} (hp : Nat.Prime p) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (n.factorization p:ℝ)) ≤ (N:ℝ)/((p:ℝ)-1) := by
  have he : (∑ n ∈ Icc 1 N, n.factorization p) = N.factorial.factorization p := by
    have hI : Finset.Icc 1 N = Finset.Ico 1 (N+1) := by
      ext n
      simp only [Finset.mem_Icc,Finset.mem_Ico]
      omega
    rw [hI, ← Nat.factorization_prod_apply (fun n hn => by
      have := (Finset.mem_Ico.mp hn).1; omega), prod_Ico_id_eq_factorial]
  have hb : (p-1) * N.factorial.factorization p ≤ N := by
    rw [Nat.sub_one_mul_factorization_factorial hp]
    exact Nat.sub_le _ _
  have hp1 : (0:ℝ) < (p:ℝ)-1 := by
    have hh : (1:ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  apply (le_div_iff₀ hp1).mpr
  rw [← Nat.cast_sum, he]
  have hb' : (((p-1):ℕ):ℝ) * N.factorial.factorization p ≤ N := by exact_mod_cast hb
  rw [Nat.cast_sub (by have := hp.two_le; omega), Nat.cast_one] at hb'
  nlinarith

theorem smooth_log_moment (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (N : ℕ) :
    (∑ n ∈ Icc 1 N, Real.log (smoothPart S n : ℝ)) ≤
      (N:ℝ) * ∑ p ∈ S, Real.log p/((p:ℝ)-1) := by
  simp_rw [log_smoothPart]
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro p hp
  rw [← sum_mul]
  have hh := mul_le_mul_of_nonneg_right (sum_factorization_le (hS p hp) N)
    (Real.log_nonneg (show (1:ℝ) ≤ p by exact_mod_cast (hS p hp).one_lt.le))
  convert hh using 1
  ring

lemma prime_log_mass_pow_two (k : ℕ) :
    (∑ p ∈ Nat.primesLE (2^k), Real.log p/((p:ℝ)-1)) ≤ 2*Real.log 4*k := by
  induction k with
  | zero => norm_num [Nat.primesLE]
  | succ k ih =>
    let A := Nat.primesLE (2^(k+1))
    have hA (p : ℕ) (hp : p ∈ A) : Nat.Prime p := (Nat.mem_primesLE.mp hp).2
    have hlo : A.filter (fun p => p ≤ 2^k) = Nat.primesLE (2^k) := by
      ext p
      simp only [A, mem_filter, Nat.mem_primesLE]
      have hpow : (2:ℕ)^k ≤ 2^(k+1) := by rw [pow_succ]; omega
      constructor
      · rintro ⟨⟨hp, hpr⟩, hpk⟩
        exact ⟨hpk, hpr⟩
      · rintro ⟨hpk, hpr⟩
        exact ⟨⟨hpk.trans hpow, hpr⟩, hpk⟩
    have hpowpos : (0:ℝ) < (2:ℝ)^k := by positivity
    have htail : (∑ p ∈ A.filter (fun p => ¬p ≤ 2^k), Real.log p/((p:ℝ)-1)) ≤
        2*Real.log 4 := by
      calc
        _ ≤ ∑ p ∈ A.filter (fun p => ¬p ≤ 2^k), Real.log p/((2:ℝ)^k) := by
          apply sum_le_sum
          intro p hp
          have hpk := (mem_filter.mp hp).2
          have hpr := hA p (mem_filter.mp hp).1
          have hd : (2:ℝ)^k ≤ (p:ℝ)-1 := by
            have hh : 2^k+1 ≤ p := by omega
            have hh' : (2:ℝ)^k+1 ≤ p := by exact_mod_cast hh
            linarith
          exact div_le_div_of_nonneg_left (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
            hpowpos hd
        _ ≤ (∑ p ∈ A, Real.log p)/((2:ℝ)^k) := by
          rw [← sum_div]
          apply div_le_div_of_nonneg_right _ hpowpos.le
          exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun p hp _ => Real.log_nonneg (by exact_mod_cast (hA p hp).one_lt.le))
        _ ≤ Real.log 4*((2:ℝ)^(k+1))/((2:ℝ)^k) := by
          apply div_le_div_of_nonneg_right _ hpowpos.le
          have hh := Chebyshev.theta_le_log4_mul_x (show (0:ℝ) ≤ (2^(k+1):ℕ) by positivity)
          rw [Chebyshev.theta_eq_sum_primesLE_log] at hh
          simpa only [Nat.cast_pow, Nat.cast_ofNat, A] using hh
        _ = _ := by rw [pow_succ]; field_simp
    have he := sum_filter_add_sum_filter_not A (fun p => p ≤ 2^k)
      (fun p => Real.log p/((p:ℝ)-1))
    rw [hlo] at he
    change (∑ p ∈ A, Real.log p/((p:ℝ)-1)) ≤ _
    rw [← he]
    push_cast
    nlinarith

theorem large_smooth_count (S : Finset ℕ) (k N : ℕ)
    (hS : S ⊆ Nat.primesLE (2^k)) {R : ℝ} (hR : 0 < R) :
    ((Finset.Icc 1 N |>.filter (fun n => R ≤ Real.log (smoothPart S n : ℝ))).card : ℝ) ≤
      (N:ℝ) * (2*Real.log 4*k)/R := by
  have hprime : ∀ p ∈ S, Nat.Prime p := fun p hp => (Nat.mem_primesLE.mp (hS hp)).2
  have hlog (n : ℕ) : 0 ≤ Real.log (smoothPart S n : ℝ) := by
    rw [log_smoothPart]
    exact sum_nonneg fun p hp => mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by exact_mod_cast (hprime p hp).one_lt.le))
  apply (le_div_iff₀ hR).mpr
  calc
    _ ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => R ≤ Real.log (smoothPart S n : ℝ)),
        Real.log (smoothPart S n : ℝ) := by
      simpa only [sum_const, nsmul_eq_mul] using
        (sum_le_sum fun n (hn : n ∈ (Finset.Icc 1 N).filter (fun n => R ≤ Real.log (smoothPart S n : ℝ)))
          => (mem_filter.mp hn).2)
    _ ≤ ∑ n ∈ Icc 1 N, Real.log (smoothPart S n : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => hlog _)
    _ ≤ (N:ℝ) * ∑ p ∈ S, Real.log p/((p:ℝ)-1) := smooth_log_moment S hprime N
    _ ≤ (N:ℝ) * (2*Real.log 4*k) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      apply (sum_le_sum_of_subset_of_nonneg hS (fun p hp _ => ?_)).trans (prime_log_mass_pow_two k)
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le))
        (by have hh : (1:ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt
            linarith)

end OrdinarySmoothRough

end

end OAI
