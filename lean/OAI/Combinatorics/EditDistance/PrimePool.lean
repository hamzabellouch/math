import Mathlib

namespace OAI

/-!
# Finite pools of distinct primes from central binomial estimates
-/

namespace EditPrimes
open scoped BigOperators
open Nat Finset

def pool (n : ℕ) : Finset ℕ := (Finset.Ioc n (2*n)).filter Nat.Prime

lemma centralBinom_le_with_primes (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤ (2*n)^(Nat.sqrt (2*n)) * 4^(2*n/3) * (2*n)^(pool n).card := by
  have hpos : 0 < n := by omega
  have h2pos : 1 ≤ 2*n := by omega
  let f (p : ℕ) := p ^ n.centralBinom.factorization p
  let S := (Finset.range (2*n+1)).filter Nat.Prime
  let T := (Finset.range (2*n/3+1)).filter Nat.Prime
  have heq : n.centralBinom = ∏ p ∈ S, f p := by
    rw [← n.prod_pow_factorization_centralBinom]
    dsimp [S,f]
    symm
    apply Finset.prod_filter_of_ne
    intro p _ h
    contrapose h
    rw [Nat.factorization_eq_zero_of_not_prime _ h,pow_zero]
  have hlow : ∏ p ∈ S.filter (· ≤ n), f p = ∏ p ∈ T, f p := by
    symm
    apply Finset.prod_subset
    · intro p hp
      obtain ⟨hp,hprime⟩ := Finset.mem_filter.mp hp
      have hb := Finset.mem_range.mp hp
      have hm : 2*n/3 ≤ n := by omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hprime⟩,by omega⟩
    · intro p hp hpT
      obtain ⟨hp,hpn⟩ := Finset.mem_filter.mp hp
      obtain ⟨_,hprime⟩ := Finset.mem_filter.mp hp
      have hb : 2*n/3 < p := by
        by_contra h
        apply hpT
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hprime⟩
      have hb' : 2*n < 3*p := by omega
      dsimp [f]
      rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpn hb',pow_zero]
  have hhigh : S.filter (fun p => ¬p ≤ n) = pool n := by
    ext p
    simp only [S,pool,Finset.mem_filter,Finset.mem_range,Finset.mem_Ioc,Nat.lt_succ_iff,not_le]
    tauto
  have hT : ∏ p ∈ T, f p ≤ (2*n)^Nat.sqrt (2*n) * 4^(2*n/3) := by
    rw [←Finset.prod_filter_mul_prod_filter_not T (· ≤ Nat.sqrt (2*n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod (fun p _ => (show f p ≤ 2*n from
        Nat.pow_factorization_choose_le (by omega)))).trans ?_
      rw [Finset.prod_const]
      apply Nat.pow_le_pow_right h2pos
      have hc : (Finset.Icc 1 (Nat.sqrt (2*n))).card = Nat.sqrt (2*n) := by
        rw [Nat.card_Icc,Nat.add_sub_cancel]
      apply (Finset.card_le_card ?_).trans hc.le
      intro p hp
      obtain ⟨hp,hs⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hp).2.one_lt.le,hs⟩
    · refine le_trans ?_ (primorial_le_four_pow (2*n/3))
      refine (Finset.prod_le_prod (fun p hp => (show f p ≤ p from ?_))).trans ?_
      · obtain ⟨hp,hs⟩ := Finset.mem_filter.mp hp
        dsimp [f]
        refine (Nat.pow_le_pow_right (Finset.mem_filter.mp hp).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp (not_le.mp hs))
      · apply Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
        intro p hp _
        exact (Finset.mem_filter.mp hp).2.one_lt.le
  rw [heq,←Finset.prod_filter_mul_prod_filter_not S (· ≤ n),hlow,hhigh]
  apply Nat.mul_le_mul hT
  calc
    ∏ p ∈ pool n, f p ≤ ∏ _p ∈ pool n, (2*n) :=
      Finset.prod_le_prod (fun _ _ => Nat.pow_factorization_choose_le (by omega))
    _ = (2*n)^(pool n).card := Finset.prod_const _

end EditPrimes

namespace EditPrimes
open scoped BigOperators
open Nat Finset Filter

lemma binomial_log_bound {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 < Real.log (n : ℝ) +
      ((Nat.sqrt (2*n) : ℝ) + (pool n).card) * Real.log (2*(n : ℝ)) +
        (2*(n : ℝ)/3) * Real.log 4 := by
  have hb := Nat.four_pow_lt_mul_centralBinom n (by omega)
  have hu := centralBinom_le_with_primes n (by omega)
  have hr : (4 : ℝ)^n < (n : ℝ) *
      ((2*(n : ℝ))^(Nat.sqrt (2*n)) * 4^(2*n/3) * (2*(n : ℝ))^(pool n).card) := by
    exact_mod_cast hb.trans_le (Nat.mul_le_mul_left n hu)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0<n by omega)
  have h2n : 0 < 2*(n : ℝ) := by positivity
  have hl := Real.log_lt_log (by positivity : 0 < (4 : ℝ)^n) hr
  rw [Real.log_mul hnR.ne' (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at hl
  simp only [Real.log_pow] at hl
  have hf : ((2*n/3 : ℕ) : ℝ) ≤ 2*(n : ℝ)/3 := by
    have h := (Nat.cast_div_le (m := 2*n) (n := 3) : ((2*n/3 : ℕ) : ℝ) ≤ ((2*n : ℕ) : ℝ)/(3 : ℝ))
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using h
  have hlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hf hlog]

lemma pool_square_large {b : ℕ} (hb : 2 ≤ b)
    (hlog : Real.log (b : ℝ) ≤ (Real.log 4 / 60) * (b : ℝ)) : b ≤ (pool (b^2)).card := by
  by_contra hcard
  have hcard : (pool (b^2)).card ≤ b := by omega
  have h := binomial_log_bound (show 4 ≤ b^2 by nlinarith)
  have bpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hs : Nat.sqrt (2*(b^2)) ≤ 2*b := by
    have hsq := Nat.sqrt_le (2*b^2)
    nlinarith
  have hsR : (Nat.sqrt (2*b^2) : ℝ) ≤ 2*(b : ℝ) := by exact_mod_cast hs
  have hcR : ((pool (b^2)).card : ℝ) ≤ b := by exact_mod_cast hcard
  have hlogb : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log (2 : ℝ) ≤ Real.log (b : ℝ) := Real.log_le_log (by norm_num) hbR
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hlogn : Real.log ((b^2 : ℕ) : ℝ) = 2 * Real.log (b : ℝ) := by
    simp only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat]
  have hlog2n : Real.log (2 * ((b^2 : ℕ) : ℝ)) ≤ 3 * Real.log (b : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity),hlogn]
    linarith
  have hlog2np : 0 ≤ Real.log (2*((b^2 : ℕ) : ℝ)) := Real.log_nonneg (by push_cast; nlinarith)
  have hterm : ((Nat.sqrt (2*b^2) : ℝ) + (pool (b^2)).card) * Real.log (2*((b^2 : ℕ) : ℝ)) ≤
      9 * (b : ℝ) * Real.log (b : ℝ) := by
    calc
      _ ≤ (3 * (b : ℝ)) * (3*Real.log (b : ℝ)) := by gcongr; linarith
      _ = _ := by ring
  rw [hlogn] at h
  push_cast at h hterm
  have hsmall : 2*Real.log (b : ℝ) + 9*(b : ℝ)*Real.log (b : ℝ) ≤ 10*(b : ℝ)*Real.log (b : ℝ) := by
    nlinarith
  have hbound := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 10*(b : ℝ) by positivity)
  nlinarith [sq_pos_of_pos bpos]

theorem eventually_pool_square : ∀ᶠ b : ℕ in Filter.atTop, b ≤ (pool (b^2)).card := by
  have hε : 0 < Real.log (4 : ℝ) / 60 := by positivity
  have hh := Real.isLittleO_log_id_atTop.def hε
  have hn : Filter.Tendsto (fun b : ℕ => (b : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [hn.eventually hh,Filter.eventually_ge_atTop (2 : ℕ)] with b hlog hb
  apply pool_square_large hb
  have hbn : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hlogb : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hbn
  simpa only [Function.id_def,Real.norm_eq_abs,abs_of_nonneg hlogb,
    abs_of_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b)] using hlog

theorem primes_of_pool {b : ℕ} (hb : b ≤ (pool (b^2)).card) :
    ∃ p : Fin b → ℕ, Function.Injective p ∧
      (∀ j, (p j).Prime) ∧ (∀ j, b^2 ≤ p j) ∧ (∀ j, p j ≤ 2*b^2) := by
  classical
  let e : Fin b ↪ (pool (b^2)) := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin,Fintype.card_coe] using hb))
  refine ⟨fun j => (e j).val, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro j
    exact (Finset.mem_filter.mp (e j).property).2
  · intro j
    exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp (e j).property).1).1.le
  · intro j
    exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp (e j).property).1).2

end EditPrimes

end OAI
