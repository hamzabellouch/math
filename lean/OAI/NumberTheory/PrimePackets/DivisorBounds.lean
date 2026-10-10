import Mathlib

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
namespace PrimeDegreePackets

 

lemma sum_divisors_initial {A : Type*} [AddCommMonoid A] (F : ℕ → ℕ → A) (N : ℕ) :
    (∑ m ∈ Icc 1 N, ∑ d ∈ m.divisors, F d (m / d)) =
      ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 (N / d), F d e := by
  classical
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun p _ => ⟨p.2, p.1 / p.2⟩)
  · intro p hp
    obtain ⟨hm, hd⟩ := mem_sigma.mp hp
    obtain ⟨hdm, hm0⟩ := Nat.mem_divisors.mp hd
    have hd0 := Nat.pos_of_mem_divisors hd
    have hdmle := Nat.le_of_dvd (by omega : 0 < p.1) hdm
    apply mem_sigma.mpr
    refine ⟨mem_Icc.mpr ⟨hd0, hdmle.trans (mem_Icc.mp hm).2⟩, mem_Icc.mpr ⟨?_, ?_⟩⟩
    · exact Nat.le_div_iff_mul_le hd0 |>.mpr (by simpa using hdmle)
    · exact Nat.div_le_div_right (mem_Icc.mp hm).2
  · intro p hp q hq hpq
    obtain ⟨hpm, hpd⟩ := mem_sigma.mp hp
    obtain ⟨hqm, hqd⟩ := mem_sigma.mp hq
    have h1 : p.2 = q.2 := congrArg Sigma.fst hpq
    have h2 : p.1 / p.2 = q.1 / q.2 := by simpa using congrArg Sigma.snd hpq
    have hm : p.1 = q.1 := by
      calc
        p.1 = p.2 * (p.1 / p.2) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hpd).1).symm
        _ = q.2 * (q.1 / q.2) := by rw [h2, h1]
        _ = q.1 := Nat.mul_div_cancel' (Nat.mem_divisors.mp hqd).1
    cases p
    cases q
    simp_all
  · intro q hq
    obtain ⟨hd, he⟩ := mem_sigma.mp hq
    have hd0 : 0 < q.1 := (mem_Icc.mp hd).1
    have he0 : 0 < q.2 := (mem_Icc.mp he).1
    have hmul : q.1 * q.2 ≤ N := by
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp (mem_Icc.mp he).2
    refine ⟨⟨q.1 * q.2, q.1⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd0 he0, hmul⟩,
      Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, by positivity⟩⟩, ?_⟩
    simp [Nat.mul_div_cancel_left _ hd0]
  · intro p hp
    rfl

 

def nFoldDivisor (k m : ℕ) : ℕ := (ArithmeticFunction.zeta ^ k) m

lemma nFoldDivisor_succ (k m : ℕ) :
    nFoldDivisor (k + 1) m = ∑ d ∈ m.divisors, nFoldDivisor k d := by
  simp only [nFoldDivisor, pow_succ, ArithmeticFunction.mul_zeta_apply]

lemma nFoldDivisor_one (m : ℕ) : nFoldDivisor 1 m = if m = 0 then 0 else 1 := by
  simp only [nFoldDivisor, pow_one]
  rfl

 
lemma nFoldDivisor_sum_succ (k N : ℕ) :
    (∑ m ∈ Icc 1 N, nFoldDivisor (k + 1) m) =
      ∑ d ∈ Icc 1 N, nFoldDivisor k d * (N / d) := by
  simp_rw [nFoldDivisor_succ]
  rw [sum_divisors_initial (fun d _ => nFoldDivisor k d)]
  simp [Nat.card_Icc, mul_comm]

lemma harmonic_real_eq_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ d ∈ Icc 1 N, (d : ℝ)⁻¹ := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

lemma harmonic_real_nonneg (N : ℕ) : 0 ≤ (harmonic N : ℝ) := by
  rw [harmonic_real_eq_sum]
  exact Finset.sum_nonneg (fun _ _ => by positivity)

lemma harmonic_real_mono {M N : ℕ} (h : M ≤ N) :
    (harmonic M : ℝ) ≤ harmonic N := by
  simp only [harmonic_real_eq_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h)
    (fun _ _ _ => by positivity)

 

lemma nFoldDivisor_reciprocal_sum (k N : ℕ) :
    (∑ m ∈ Icc 1 N, (nFoldDivisor k m : ℝ) / m) ≤ (harmonic N : ℝ) ^ k := by
  induction k with
  | zero =>
    simp only [nFoldDivisor, pow_zero, ArithmeticFunction.one_apply]
    by_cases hN : 1 ≤ N
    · simp [ite_div, hN]
    · have : N = 0 := by omega
      simp [this]
  | succ k ih =>
    have hc : (∑ m ∈ Icc 1 N, (nFoldDivisor (k + 1) m : ℝ) / m) =
        ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 (N / d), (nFoldDivisor k d : ℝ) / (d * e) := by
      simp_rw [nFoldDivisor_succ, Nat.cast_sum, Finset.sum_div]
      have hid := sum_divisors_initial (fun d e => (nFoldDivisor k d : ℝ) / (d * e)) N
      convert hid using 1
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
    rw [hc]
    calc
      _ = ∑ d ∈ Icc 1 N, ((nFoldDivisor k d : ℝ) / d) * harmonic (N / d) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [harmonic_real_eq_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ ∑ d ∈ Icc 1 N, ((nFoldDivisor k d : ℝ) / d) * harmonic N := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (harmonic_real_mono (Nat.div_le_self _ _)) (by positivity)
      _ = (∑ d ∈ Icc 1 N, (nFoldDivisor k d : ℝ) / d) * harmonic N := by rw [Finset.sum_mul]
      _ ≤ (harmonic N : ℝ) ^ k * harmonic N :=
        mul_le_mul_of_nonneg_right ih (harmonic_real_nonneg N)
      _ = (harmonic N : ℝ) ^ (k + 1) := (pow_succ _ _).symm

 

theorem nFoldDivisor_summatory_le (k N : ℕ) :
    (∑ m ∈ Icc 1 N, (nFoldDivisor (k + 1) m : ℝ)) ≤
      N * (1 + Real.log N) ^ k := by
  have hsum : (∑ m ∈ Icc 1 N, (nFoldDivisor (k + 1) m : ℝ)) =
      ∑ d ∈ Icc 1 N, (nFoldDivisor k d : ℝ) * (N / d : ℕ) := by
    exact_mod_cast nFoldDivisor_sum_succ k N
  rw [hsum]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, (nFoldDivisor k d : ℝ) * ((N : ℝ) / d) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left ((Nat.cast_div_le)) (by positivity)
    _ = (N : ℝ) * ∑ d ∈ Icc 1 N, (nFoldDivisor k d : ℝ) / d := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ (N : ℝ) * (harmonic N : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left (nFoldDivisor_reciprocal_sum k N) (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (harmonic_real_nonneg N) (harmonic_le_one_add_log N) k

 
theorem nFoldDivisor_summatory_real (k : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (∑ m ∈ Icc 1 ⌊z⌋₊, (nFoldDivisor (k + 1) m : ℝ)) ≤
      z * (1 + Real.log z) ^ k := by
  have hfloor : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hfloor1 : 1 ≤ ⌊z⌋₊ := by exact Nat.le_floor (by simpa using hz)
  have hlog : Real.log (⌊z⌋₊ : ℝ) ≤ Real.log z :=
    Real.log_le_log (by exact_mod_cast (show 0 < ⌊z⌋₊ by omega)) hfloor
  have hbase : 0 ≤ 1 + Real.log (⌊z⌋₊ : ℝ) := by
    have : 0 ≤ Real.log (⌊z⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hfloor1)
    linarith
  exact (nFoldDivisor_summatory_le k ⌊z⌋₊).trans
    (mul_le_mul hfloor (pow_le_pow_left₀ hbase (by linarith) k)
      (pow_nonneg hbase _) (by linarith))

 

theorem nFoldDivisor_prime_pow (k j p : ℕ) (hp : p.Prime) :
    nFoldDivisor (k + 1) (p ^ j) = (j + k).choose k := by
  induction k generalizing j with
  | zero => simp [nFoldDivisor_one, hp.ne_zero]
  | succ k ih =>
    rw [nFoldDivisor_succ, Nat.sum_divisors_prime_pow hp]
    simp_rw [ih]
    simpa [Nat.add_assoc] using Nat.sum_range_add_choose j k

 
theorem nFoldDivisor_prime_pow_le (k j p : ℕ) (hp : p.Prime) :
    nFoldDivisor (k + 1) (p ^ j) ≤ (k + 1) ^ j := by
  rw [nFoldDivisor_prime_pow k j p hp]
  calc
    (j + k).choose k = (k + j).choose j := by
      rw [Nat.add_comm j k, Nat.choose_symm_add]
    _ ≤ (k + 1) ^ j := Nat.choose_add_le_add_one_pow k j

 
lemma choose_mul_geometric_le (k j : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ((j + k).choose k : ℝ) * r ^ j ≤ 1 / (1 - r) ^ (k + 1) := by
  have H := hasSum_choose_mul_geometric_of_norm_lt_one k
    (show ‖r‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
  rw [← H.tsum_eq]
  exact H.summable.le_tsum j (fun m _ => by positivity)

 

lemma nFoldDivisor_prime_pow_rpow (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p j : ℕ, p.Prime →
      (nFoldDivisor (k + 1) (p ^ j) : ℝ) ≤ C * ((p : ℝ) ^ j) ^ ε := by
  let r : ℝ := (2 : ℝ) ^ (-ε)
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hrlt : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let C : ℝ := 1 / (1 - r) ^ (k + 1)
  have hC : 1 ≤ C := by
    simpa [C] using choose_mul_geometric_le k 0 r hrpos.le hrlt
  refine ⟨C, hC, ?_⟩
  intro p j hp
  have H := choose_mul_geometric_le k j r hrpos.le hrlt
  rw [nFoldDivisor_prime_pow k j p hp]
  have hr : r ^ j = (((2 : ℝ) ^ j) ^ ε)⁻¹ := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      neg_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), mul_comm ε (j : ℝ), Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hr] at H
  have H' : ((j + k).choose k : ℝ) ≤ C * (((2 : ℝ) ^ j) ^ ε) := by
    exact (mul_inv_le_iff₀ (Real.rpow_pos_of_pos (by positivity) ε)).mp H
  apply H'.trans
  apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ C)
  apply Real.rpow_le_rpow (by positivity) _ hε.le
  exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp.two_le) j

 

theorem nFoldDivisor_subpolynomial (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, (nFoldDivisor (k + 1) m : ℝ) ≤ C * (m : ℝ) ^ ε := by
  classical
  obtain ⟨C₀, hC₀, hsmall⟩ := nFoldDivisor_prime_pow_rpow k ε hε
  have hlarge : ∀ᶠ p : ℕ in Filter.atTop, (k + 1 : ℝ) ≤ (p : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (k + 1 : ℝ))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨C₀ ^ N, by positivity, ?_⟩
  intro m
  by_cases hm : m = 0
  · subst m
    simp [nFoldDivisor, Real.zero_rpow hε.ne']
  have hfactor := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    (ArithmeticFunction.zeta ^ (k + 1)) (ArithmeticFunction.isMultiplicative_zeta.pow) hm
  have hfactorR : (nFoldDivisor (k + 1) m : ℝ) =
      ∏ p ∈ m.factorization.support, (nFoldDivisor (k + 1) (p ^ m.factorization p) : ℝ) := by
    exact_mod_cast hfactor
  rw [hfactorR]
  calc
    _ ≤ ∏ p ∈ m.factorization.support,
        (if p < N then C₀ else 1) * ((p : ℝ) ^ m.factorization p) ^ ε := by
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro p hp
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      by_cases hpN : p < N
      · simpa [hpN] using hsmall p (m.factorization p) hprime
      · simp only [ite_eq_right hpN, one_mul]
        calc
          _ ≤ ((k + 1 : ℝ) ^ m.factorization p) := by
            exact_mod_cast nFoldDivisor_prime_pow_le k (m.factorization p) p hprime
          _ ≤ ((p : ℝ) ^ ε) ^ m.factorization p :=
            pow_le_pow_left₀ (by positivity) (hN p (by omega)) _
          _ = ((p : ℝ) ^ m.factorization p) ^ ε := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm,
              Real.rpow_natCast_mul (Nat.cast_nonneg p)]
    _ = (∏ p ∈ m.factorization.support with p < N, C₀) *
        (∏ p ∈ m.factorization.support, ((p : ℝ) ^ m.factorization p) ^ ε) := by
      rw [Finset.prod_mul_distrib, ← Finset.prod_filter]
    _ ≤ C₀ ^ N * (∏ p ∈ m.factorization.support,
        ((p : ℝ) ^ m.factorization p) ^ ε) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        _ ≤ ∏ p ∈ Finset.range N, C₀ := by
          apply Finset.prod_le_prod_of_subset_of_one_le₀
          · intro p hp
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
          · intro p _
            linarith
          · intro p _ _
            exact hC₀
        _ = C₀ ^ N := by simp
    _ = C₀ ^ N * (m : ℝ) ^ ε := by
      congr 1
      rw [Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
      congr 1
      exact_mod_cast Nat.prod_factorization_pow_eq_self hm

end PrimeDegreePackets


namespace PrimeDegreePackets
open Finset Nat

 
def IsPowerful (m : ℕ) : Prop := m ≠ 0 ∧ ∀ p ∈ m.primeFactors, 2 ≤ m.factorization p

lemma powerful_square_cube {m : ℕ} (hm : IsPowerful m) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ^ 2 * b ^ 3 = m := by
  obtain ⟨b, c, hb, hc, hbc, hbs⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hm.1)
  have hbcdiv : b ∣ c := by
    apply (Nat.factorization_le_iff_dvd (by omega : b ≠ 0) (by omega : c ≠ 0)).mp
    intro p
    by_cases hp0 : b.factorization p = 0
    · simp [hp0]
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hp0)
    have hpb : p ∣ b := (hp.dvd_iff_one_le_factorization (by omega : b ≠ 0)).mpr (by omega)
    have hpm : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr
      ⟨hp, hbc ▸ dvd_mul_of_dvd_right hpb (c^2), hm.1⟩
    have htwo := hm.2 p hpm
    have hbone := hbs.natFactorization_le_one p
    have heq : m.factorization p = 2 * c.factorization p + b.factorization p := by
      rw [← hbc, Nat.factorization_mul (by positivity) (by omega : b ≠ 0), Nat.factorization_pow]
      simp
    omega
  obtain ⟨a, ha⟩ := hbcdiv
  have ha0 : 0 < a := by
    by_contra h
    have : a = 0 := by omega
    simp [this] at ha
    omega
  refine ⟨a, b, ha0, hb, ?_⟩
  rw [← hbc, ha]
  ring

 

def powerfulCorrection (k m : ℕ) : ℝ := by
  classical
  exact if IsPowerful m then (nFoldDivisor (k + 1) m : ℝ) else 0

lemma powerfulCorrection_nonneg (k m : ℕ) : 0 ≤ powerfulCorrection k m := by
  unfold powerfulCorrection
  split_ifs <;> positivity

lemma powerfulCorrection_zero (k : ℕ) : powerfulCorrection k 0 = 0 := by
  simp [powerfulCorrection, IsPowerful]

noncomputable def powerfulRepresentation (m : {m : ℕ // IsPowerful m}) : ℕ × ℕ :=
  ⟨(powerful_square_cube m.property).choose,
    ((powerful_square_cube m.property).choose_spec).choose⟩

lemma powerfulRepresentation_spec (m : {m : ℕ // IsPowerful m}) :
    0 < (powerfulRepresentation m).1 ∧ 0 < (powerfulRepresentation m).2 ∧
      (powerfulRepresentation m).1 ^ 2 * (powerfulRepresentation m).2 ^ 3 = m := by
  exact ((powerful_square_cube m.property).choose_spec).choose_spec

lemma powerfulRepresentation_injective : Function.Injective powerfulRepresentation := by
  intro m n h
  apply Subtype.ext
  calc
    (m : ℕ) = (powerfulRepresentation m).1^2 * (powerfulRepresentation m).2^3 := (powerfulRepresentation_spec m).2.2.symm
    _ = (n : ℕ) := by rw [h]; exact (powerfulRepresentation_spec n).2.2

end PrimeDegreePackets


namespace PrimeDegreePackets
open Finset Nat

lemma powerful_rpow_summable :
    Summable (fun m : {m : ℕ // IsPowerful m} => ((m : ℕ) : ℝ) ^ (-(5:ℝ)/8)) := by
  have ha : Summable (fun a : ℕ => (a : ℝ)^(-(5:ℝ)/4)) := Real.summable_nat_rpow.mpr (by norm_num)
  have hb : Summable (fun b : ℕ => (b : ℝ)^(-(15:ℝ)/8)) := Real.summable_nat_rpow.mpr (by norm_num)
  have hab := ha.mul_of_nonneg hb (fun a => Real.rpow_nonneg (Nat.cast_nonneg a) _)
    (fun b => Real.rpow_nonneg (Nat.cast_nonneg b) _)
  apply (hab.comp_injective powerfulRepresentation_injective).congr
  intro m
  have hm := (powerfulRepresentation_spec m).2.2
  have ha0 : 0 ≤ (((powerfulRepresentation m).1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hb0 : 0 ≤ (((powerfulRepresentation m).2 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [← hm, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast_mul ha0, ← Real.rpow_natCast_mul hb0]
  norm_num

 

theorem powerfulCorrection_summable (k : ℕ) :
    Summable (fun m : ℕ => powerfulCorrection k m / (m : ℝ)^((3:ℝ)/4)) := by
  obtain ⟨C, hC, hbound⟩ := nFoldDivisor_subpolynomial k ((1:ℝ)/8) (by norm_num)
  have H : Summable (fun m : {m : ℕ // IsPowerful m} =>
      (nFoldDivisor (k+1) m : ℝ) / ((m : ℕ) : ℝ)^((3:ℝ)/4)) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (powerful_rpow_summable.mul_left C)
    intro m
    have hm : 0 < ((m : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero m.property.1
    calc
      _ ≤ (C * ((m : ℕ) : ℝ)^((1:ℝ)/8)) / ((m : ℕ) : ℝ)^((3:ℝ)/4) :=
        div_le_div_of_nonneg_right (hbound m) (Real.rpow_nonneg hm.le _)
      _ = C * ((m : ℕ) : ℝ)^(-(5:ℝ)/8) := by
        rw [mul_div_assoc, ← Real.rpow_sub hm]
        norm_num
  have Hind := (summable_subtype_iff_indicator
    (f := fun m : ℕ => (nFoldDivisor (k+1) m : ℝ) / (m : ℝ)^((3:ℝ)/4))
    (s := {m : ℕ | IsPowerful m})).mp H
  apply Hind.congr
  intro m
  by_cases hm : IsPowerful m <;> simp [powerfulCorrection, Set.indicator, hm]

noncomputable def powerfulMoment (k : ℕ) : ℝ :=
  ∑' m : ℕ, powerfulCorrection k m / (m : ℝ)^((3:ℝ)/4)

lemma powerfulMoment_nonneg (k : ℕ) : 0 ≤ powerfulMoment k := by
  exact tsum_nonneg (fun m => div_nonneg (powerfulCorrection_nonneg k m) (Real.rpow_nonneg (Nat.cast_nonneg m) _))

lemma powerfulCorrection_moment_sum_le (k : ℕ) (s : Finset ℕ) :
    (∑ m ∈ s, powerfulCorrection k m / (m : ℝ)^((3:ℝ)/4)) ≤ powerfulMoment k :=
  (powerfulCorrection_summable k).sum_le_tsum s
    (fun m _ => div_nonneg (powerfulCorrection_nonneg k m) (Real.rpow_nonneg (Nat.cast_nonneg m) _))

end PrimeDegreePackets


namespace PrimeDegreePackets
open Finset Nat

lemma powerfulCorrection_reciprocal_sum_le (k : ℕ) (s : Finset ℕ) :
    (∑ m ∈ s, powerfulCorrection k m / (m : ℝ)) ≤ powerfulMoment k := by
  apply (Finset.sum_le_sum (g := fun m => powerfulCorrection k m / (m : ℝ)^((3:ℝ)/4)) ?_).trans
    (powerfulCorrection_moment_sum_le k s)
  intro m _
  by_cases hm : m = 0
  · simp [hm]
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm)
  apply div_le_div_of_nonneg_left (powerfulCorrection_nonneg k m) (by positivity)
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num : (3:ℝ)/4 ≤ 1)

lemma powerfulCorrection_reciprocal_identity (k : ℕ) (m : ℕ) (hm : m ≠ 0) :
    powerfulCorrection k m / (m : ℝ) =
      (powerfulCorrection k m / (m : ℝ)^((3:ℝ)/4)) * (m : ℝ)^(-(1:ℝ)/4) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.rpow_neg hm0.le, mul_assoc,
    ← Real.rpow_add hm0]
  norm_num [Real.rpow_neg_one]

 
theorem powerfulCorrection_reciprocal_tail (k : ℕ) (s : Finset ℕ) (T : ℝ)
    (hT : 0 < T) (hs : ∀ m ∈ s, T ≤ (m : ℝ)) :
    (∑ m ∈ s, powerfulCorrection k m / (m : ℝ)) ≤ T^(-(1:ℝ)/4) * powerfulMoment k := by
  calc
    _ ≤ ∑ m ∈ s, T^(-(1:ℝ)/4) * (powerfulCorrection k m / (m : ℝ)^((3:ℝ)/4)) := by
      apply Finset.sum_le_sum
      intro m hm
      have hm0 : m ≠ 0 := by
        have := hT.trans_le (hs m hm)
        exact_mod_cast this.ne'
      rw [powerfulCorrection_reciprocal_identity k m hm0, mul_comm]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hT (hs m hm) (by norm_num))
        (div_nonneg (powerfulCorrection_nonneg k m) (Real.rpow_nonneg (Nat.cast_nonneg m) _))
    _ = T^(-(1:ℝ)/4) * ∑ m ∈ s, powerfulCorrection k m / (m : ℝ)^((3:ℝ)/4) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (powerfulCorrection_moment_sum_le k s) (Real.rpow_nonneg hT.le _)

end PrimeDegreePackets
end
end

end OAI
