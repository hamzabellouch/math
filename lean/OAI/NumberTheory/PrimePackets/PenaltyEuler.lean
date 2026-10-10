import Mathlib
import OAI.NumberTheory.PrimePackets.IntervalSieve

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
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
namespace PrimeDegreePackets.Sieve
open Finset Nat

def smallPrimes (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime

def penaltyEuler (g : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∏ p ∈ smallPrimes N, (1 + g p / ((p : ℝ) - 1))

lemma penaltyEuler_one_le (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p) (N : ℕ) :
    1 ≤ penaltyEuler g N := by
  apply Finset.one_le_prod₀
  intro p hp
  have hp1 : 1 < (p : ℝ) := by
    exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
  exact le_add_of_nonneg_right (div_nonneg (hg p) (by linarith))

lemma penaltyEuler_mono (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p)
    {N M : ℕ} (hNM : N ≤ M) : penaltyEuler g N ≤ penaltyEuler g M := by
  apply Finset.prod_le_prod_of_subset_of_one_le₀
  · exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hNM)
  · intro p hp
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    exact add_nonneg (by norm_num) (div_nonneg (hg p) (by linarith))
  · intro p hp _
    have hp1 : 1 < (p : ℝ) := by
      exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    exact le_add_of_nonneg_right (div_nonneg (hg p) (by linarith))

lemma primePenalty_le_softWeight (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) {m : ℕ} (hm : m ≠ 0) :
    primePenalty g m ≤ softWeight S g m := by
  have hsoft : softWeight S g m = ∏ p ∈ S.filter (· ∣ m), g p := by
    rw [softWeight, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p hp
    by_cases hpd : p ∣ m
    · simp [hpd, (hS p hp).coprime_iff_not_dvd]
    · simp [hpd, (hS p hp).coprime_iff_not_dvd]
  have hsub : S.filter (· ∣ m) ⊆ m.primeFactors := by
    intro p hp
    obtain ⟨hpS, hpd⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hS p hpS, hpd, hm⟩
  rw [primePenalty_apply g hm, hsoft, ← Finset.prod_sdiff hsub]
  have hrem : (∏ p ∈ m.primeFactors \ S.filter (· ∣ m), g p) ≤ 1 :=
    Finset.prod_le_one₀ (fun prime _ => (hg prime).1) (fun prime _ => (hg prime).2)
  simpa using mul_le_mul_of_nonneg_right hrem
    (Finset.prod_nonneg (fun p _ => (hg p).1))

lemma primePenalty_interval_bound (g : ℕ → ℝ)
    (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (a b z B : ℕ)
    (hab : a ≤ b) (hz : 1 ≤ z) (hzB : z ≤ B) :
    (∑ m ∈ Finset.Ioc a b, primePenalty g m) ≤
      (((b : ℝ) - a) / Real.log (z + 1)) * penaltyEuler g B +
        ((z : ℝ) * (z + 1)) ^ 2 := by
  apply (Finset.sum_le_sum (s := Finset.Ioc a b) (g := softWeight (smallPrimes B) g) ?_).trans
    (soft_interval_bound a b z (smallPrimes B) g hab hz ?_ ?_ hg)
  · intro m hm
    exact primePenalty_le_softWeight _ (fun p hp => (Finset.mem_filter.mp hp).2) g hg
      (by have := (Finset.mem_Ioc.mp hm).1; omega)
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p hp hpz
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_le, hpz.trans hzB⟩, hp⟩

lemma interval_div_length_le (a b e : ℕ) (he : 0 < e) :
    ((b / e : ℕ) : ℝ) - (a / e : ℕ) ≤ ((b : ℝ) - a) / e + 1 := by
  have heR : 0 < (e : ℝ) := by exact_mod_cast he
  have hb : ((b / e : ℕ) : ℝ) * e ≤ b := by exact_mod_cast Nat.div_mul_le_self b e
  have ha : (a : ℝ) < (((a / e : ℕ) : ℝ) + 1) * e := by
    exact_mod_cast (Nat.div_lt_iff_lt_mul he).mp (Nat.lt_succ_self (a / e))
  calc
    _ ≤ ((b : ℝ) - a + e) / e := (le_div_iff₀ heR).mpr (by nlinarith)
    _ = _ := by rw [add_div, div_self heR.ne']

lemma sum_le_mul_sum_reciprocal (F : ℕ → ℝ) (hF : ∀ m, 0 ≤ F m) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, F m) ≤
      N * ∑ m ∈ Finset.Icc 1 N, F m / m := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  obtain ⟨hm0, hmN⟩ := Finset.mem_Icc.mp hm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  calc
    F m = m * (F m / m) := by field_simp
    _ ≤ N * (F m / m) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hmN) (div_nonneg (hF m) hmR.le)

lemma primePenalty_pow_reciprocal_le (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p)
    (k N B : ℕ) (hNB : N ≤ B) :
    (∑ m ∈ Finset.Icc 1 N, ((primePenalty g) ^ k) m / m) ≤
      (penaltyEuler g B) ^ k := by
  exact (sum_primePenalty_pow_reciprocal_le g hg k N).trans
    (pow_le_pow_left₀ ((zero_le_one : (0 : ℝ) ≤ 1).trans (penaltyEuler_one_le g hg N))
      (penaltyEuler_mono g hg hNB) k)

 

theorem sum_primePenalty_largeFactor_bound (g : ℕ → ℝ)
    (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (k a b H z : ℕ)
    (hab : a ≤ b) (hz : 1 ≤ z) (hzb : z ≤ b) :
    (∑ m ∈ Finset.Ioc a b, largeFactorConvolution (primePenalty g) k H m) ≤
      (penaltyEuler g b) ^ k *
       ((((b : ℝ) - a) / Real.log (z + 1)) * penaltyEuler g b +
        (b / (H + 1) : ℕ) *
          (penaltyEuler g b / Real.log (z + 1) + ((z : ℝ) * (z + 1)) ^ 2)) := by
  let E := penaltyEuler g b
  let L := Real.log (z + 1)
  let R := ((z : ℝ) * (z + 1)) ^ 2
  let N := b / (H + 1)
  let F := ((primePenalty g) ^ k)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < z + 1 by omega))
  have hE : 0 ≤ E := (zero_le_one : (0 : ℝ) ≤ 1).trans (penaltyEuler_one_le g (fun p => (hg p).1) b)
  have hR : 0 ≤ R := sq_nonneg _
  have hy : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hF : ∀ m, 0 ≤ F m := convolution_pow_nonneg (primePenalty_nonneg g (fun p => (hg p).1)) k
  have hNM : N ≤ b := Nat.div_le_self _ _
  have hrec : (∑ e ∈ Finset.Icc 1 N, F e / e) ≤ E ^ k :=
    primePenalty_pow_reciprocal_le g (fun p => (hg p).1) k N b hNM
  have hsum : (∑ e ∈ Finset.Icc 1 N, F e) ≤ N * E ^ k :=
    (sum_le_mul_sum_reciprocal F hF N).trans
      (mul_le_mul_of_nonneg_left hrec (Nat.cast_nonneg N))
  calc
    _ ≤ ∑ e ∈ Finset.Icc 1 N, F e *
        ∑ d ∈ Finset.Ioc (a / e) (b / e), primePenalty g d :=
      sum_largeFactorConvolution_le _ (primePenalty_nonneg g (fun p => (hg p).1)) k a b H
    _ ≤ ∑ e ∈ Finset.Icc 1 N, F e *
        (((((b : ℝ) - a) / e + 1) / L) * E + R) := by
      apply Finset.sum_le_sum
      intro e he
      apply mul_le_mul_of_nonneg_left _ (hF e)
      apply (primePenalty_interval_bound g hg (a / e) (b / e) z b
        (Nat.div_le_div_right hab) hz hzb).trans
      exact _root_.add_le_add
        (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right
            (interval_div_length_le a b e (Finset.mem_Icc.mp he).1) hL.le) hE) (le_refl R)
    _ = (((b : ℝ) - a) / L * E) * (∑ e ∈ Finset.Icc 1 N, F e / e) +
          (E / L + R) * (∑ e ∈ Finset.Icc 1 N, F e) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ ≤ (((b : ℝ) - a) / L * E) * E ^ k + (E / L + R) * (N * E ^ k) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hrec (mul_nonneg (div_nonneg hy hL.le) hE))
        (mul_le_mul_of_nonneg_left hsum (add_nonneg (div_nonneg hE hL.le) hR))
    _ = _ := by ring

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

lemma sum_primePenalty_largeFactor_bound' (g : ℕ → ℝ)
    (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (k a b H z : ℕ)
    (hab : a ≤ b) (hz : 1 ≤ z) (hzb : z ≤ b) :
    (∑ m ∈ Finset.Ioc a b, largeFactorConvolution (primePenalty g) k H m) ≤
      (penaltyEuler g b) ^ (k + 1) *
       (((b : ℝ) - a) / Real.log (z + 1) +
        (b / (H + 1) : ℕ) *
          ((Real.log (z + 1))⁻¹ + ((z : ℝ) * (z + 1)) ^ 2)) := by
  have hE := penaltyEuler_one_le g (fun p => (hg p).1) b
  have hE0 : 0 ≤ penaltyEuler g b := by linarith
  have hR : 0 ≤ ((z : ℝ) * (z + 1)) ^ 2 := sq_nonneg _
  apply (sum_primePenalty_largeFactor_bound g hg k a b H z hab hz hzb).trans
  rw [pow_succ (penaltyEuler g b) k, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hE0 k)
  have hNR : 0 ≤ (b / (H + 1) : ℕ) * ((z : ℝ) * (z + 1)) ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) hR
  have hx := mul_le_mul_of_nonneg_right hE hNR
  simp only [one_mul] at hx
  simp only [div_eq_mul_inv]
  nlinarith only [hx]

 

theorem primePenalty_pow_interval_finite (g : ℕ → ℝ)
    (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (k a b H z : ℕ)
    (hab : a ≤ b) (hH : 1 ≤ H) (hz : 1 ≤ z) (hzb : z ≤ b)
    (hTb : H ^ (2 * (k + 1)) ≤ b) :
    (∑ m ∈ Finset.Ioc a b, ((primePenalty g) ^ (k + 1)) m) ≤
      (penaltyEuler g b) ^ (k + 1) *
        ((H ^ (2 * (k + 1)) : ℕ) + 2 * ((k + 1 : ℕ) : ℝ) *
          (((b : ℝ) - a) / Real.log (z + 1) +
            (b / (H + 1) : ℕ) *
              ((Real.log (z + 1))⁻¹ + ((z : ℝ) * (z + 1)) ^ 2))) := by
  let f := primePenalty g
  let T := H ^ (2 * (k + 1))
  let E := penaltyEuler g b
  have hf : ∀ m, 0 ≤ f m := primePenalty_nonneg g (fun p => (hg p).1)
  have hFn : ∀ m, 0 ≤ (f ^ (k + 1)) m := convolution_pow_nonneg hf _
  have hTpos : 0 < T := pow_pos (by omega) _
  have hpoint : ∀ m ∈ Finset.Ioc a b, (f ^ (k + 1)) m ≤
      (if m ≤ T then (f ^ (k + 1)) m else 0) +
        2 * ((k + 1 : ℕ) : ℝ) * largeFactorConvolution f k H m := by
    intro m _
    split_ifs with hmT
    · exact le_add_of_nonneg_right (mul_nonneg (by positivity)
        (largeFactorConvolution_nonneg hf _ _ _))
    · rw [zero_add]
      apply convolution_pow_le_largeFactor hf k H m hH (by omega)
      have hTm : (T : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hmT))
      have hl := Real.log_le_log (by exact_mod_cast hTpos) hTm
      simpa [T, Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        mul_assoc] using hl
  have hsmall : (∑ m ∈ Finset.Ioc a b, if m ≤ T then (f ^ (k + 1)) m else 0) ≤
      T * E ^ (k + 1) := by
    rw [← Finset.sum_filter]
    calc
      _ ≤ ∑ m ∈ Finset.Icc 1 T, (f ^ (k + 1)) m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          obtain ⟨hm, hmT⟩ := Finset.mem_filter.mp hm
          exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Ioc.mp hm).1; omega, hmT⟩
        · intro m _ _
          exact hFn m
      _ ≤ T * ∑ m ∈ Finset.Icc 1 T, (f ^ (k + 1)) m / m :=
        sum_le_mul_sum_reciprocal _ hFn T
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (primePenalty_pow_reciprocal_le g (fun p => (hg p).1) (k + 1) T b hTb)
        (Nat.cast_nonneg T)
  have hlarge := sum_primePenalty_largeFactor_bound' g hg k a b H z hab hz hzb
  calc
    _ ≤ ∑ m ∈ Finset.Ioc a b,
        ((if m ≤ T then (f ^ (k + 1)) m else 0) +
          2 * ((k + 1 : ℕ) : ℝ) * largeFactorConvolution f k H m) :=
      Finset.sum_le_sum hpoint
    _ = (∑ m ∈ Finset.Ioc a b, if m ≤ T then (f ^ (k + 1)) m else 0) +
        2 * ((k + 1 : ℕ) : ℝ) * (∑ m ∈ Finset.Ioc a b, largeFactorConvolution f k H m) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ T * E ^ (k + 1) + 2 * ((k + 1 : ℕ) : ℝ) *
        ((penaltyEuler g b) ^ (k + 1) *
          (((b : ℝ) - a) / Real.log (z + 1) +
            (b / (H + 1) : ℕ) *
              ((Real.log (z + 1))⁻¹ + ((z : ℝ) * (z + 1)) ^ 2))) := by
      exact _root_.add_le_add hsmall (mul_le_mul_of_nonneg_left hlarge (by positivity))
    _ = _ := by dsimp [T, E]; ring

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

 

lemma sieve_error_scaled (z b N T n : ℝ) (hz : 1 ≤ z)
    (hN : 0 ≤ N) (hT : 0 ≤ T) (hn : 0 ≤ n)
    (hTz : T * z ^ 2 ≤ b) (hNz : N * z ^ 6 ≤ b) :
    T * Real.log (z + 1) + 2 * n * N *
      (1 + Real.log (z + 1) * (z * (z + 1)) ^ 2) ≤ (1 + 10 * n) * b / z := by
  have hz0 : 0 < z := by linarith
  have hL0 : 0 ≤ Real.log (z + 1) := Real.log_nonneg (by linarith)
  have hL : Real.log (z + 1) ≤ z := by
    have ht := Real.log_le_sub_one_of_pos (show 0 < z + 1 by linarith)
    linarith
  have hR : (z * (z + 1)) ^ 2 ≤ 4 * z ^ 4 := by
    have ht : z + 1 ≤ 2 * z := by linarith
    have hu := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ z + 1) ht 2
    nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hu)]
  have hz6 : z ≤ z ^ 6 := by
    simpa using (pow_le_pow_right₀ hz (show 1 ≤ 6 by omega))
  have hLR : Real.log (z + 1) * (z * (z + 1)) ^ 2 ≤ 4 * z ^ 5 := by
    calc
      _ ≤ z * (4 * z ^ 4) := mul_le_mul hL hR (sq_nonneg _) (le_trans (by norm_num) hz)
      _ = _ := by ring
  have hpoly : z * (1 + Real.log (z + 1) * (z * (z + 1)) ^ 2) ≤ 5 * z ^ 6 := by
    have ht := mul_le_mul_of_nonneg_left hLR hz0.le
    nlinarith only [ht, hz6]
  have hsmall : T * Real.log (z + 1) * z ≤ b := by
    calc
      _ ≤ T * z * z := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hL hT) hz0.le
      _ = T * z ^ 2 := by ring
      _ ≤ b := hTz
  have hlarge : N * (1 + Real.log (z + 1) * (z * (z + 1)) ^ 2) * z ≤ 5 * b := by
    calc
      _ = N * (z * (1 + Real.log (z + 1) * (z * (z + 1)) ^ 2)) := by ring
      _ ≤ N * (5 * z ^ 6) := mul_le_mul_of_nonneg_left hpoly hN
      _ = 5 * (N * z ^ 6) := by ring
      _ ≤ 5 * b := by linarith
  apply (le_div_iff₀ hz0).mpr
  have ht := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ 2 * n by positivity)
  nlinarith only [ht, hsmall]

lemma primePenalty_pow_interval_at_level (g : ℕ → ℝ)
    (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (k a b z : ℕ) (η : ℝ)
    (hab : a ≤ b) (hz : 2 ≤ z) (_hη : 0 < η)
    (hrel : η * b ≤ (b : ℝ) - a)
    (hsize : 1 + 10 * ((k + 1 : ℕ) : ℝ) ≤ η * z)
    (hroot : z ^ (12 * (k + 1) + 2) ≤ b)
    (hroot' : b < (z + 1) ^ (12 * (k + 1) + 2)) :
    (∑ m ∈ Finset.Ioc a b, ((primePenalty g) ^ (k + 1)) m) ≤
      ((12 * (k + 1) + 2 : ℕ) : ℝ) * (2 * ((k + 1 : ℕ) : ℝ) + 1) *
        (((b : ℝ) - a) / Real.log b) * (penaltyEuler g b) ^ (k + 1) := by
  let n : ℝ := (k + 1 : ℕ)
  let H := z ^ 6
  let T := H ^ (2 * (k + 1))
  let N := b / (H + 1)
  let L := Real.log ((z : ℝ) + 1)
  let R := ((z : ℝ) * (z + 1)) ^ 2
  let E := (penaltyEuler g b) ^ (k + 1)
  have hz1 : 1 ≤ z := by omega
  have hzR : 1 ≤ (z : ℝ) := by exact_mod_cast hz1
  have hz0 : 0 < (z : ℝ) := by linarith
  have hzb : z ≤ b := (Nat.le_self_pow (by omega : 12 * (k + 1) + 2 ≠ 0) z).trans hroot
  have hb1 : 1 < (b : ℝ) := by exact_mod_cast (show 1 < b by omega)
  have hb0 : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  have hL : 0 < L := Real.log_pos (by linarith)
  have hE : 0 ≤ E := pow_nonneg
    ((zero_le_one : (0 : ℝ) ≤ 1).trans (penaltyEuler_one_le g (fun p => (hg p).1) b)) _
  have hH : 1 ≤ H := one_le_pow₀ hz1
  have hTb : T ≤ b := by
    dsimp [T, H]
    rw [← pow_mul]
    apply (Nat.pow_le_pow_right hz1 (show 6 * (2 * (k + 1)) ≤ 12 * (k + 1) + 2 by omega)).trans hroot
  have hTz : (T : ℝ) * (z : ℝ) ^ 2 ≤ b := by
    have hnat : T * z ^ 2 = z ^ (12 * (k + 1) + 2) := by
      dsimp [T, H]
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    exact_mod_cast (hnat ▸ hroot)
  have hNz : (N : ℝ) * (z : ℝ) ^ 6 ≤ b := by
    have hNat : N * H ≤ b := (Nat.mul_le_mul_left N (Nat.le_succ H)).trans (Nat.div_mul_le_self b (H + 1))
    exact_mod_cast hNat
  have herr := sieve_error_scaled (z : ℝ) b N T n hzR (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by positivity) hTz hNz
  have hsize' : (1 + 10 * n) * (b : ℝ) / z ≤ η * b := by
    apply (div_le_iff₀ hz0).mpr
    have ht := mul_le_mul_of_nonneg_right hsize hb0
    dsimp [n]
    nlinarith only [ht]
  have herr' : (T : ℝ) * L + 2 * n * N * (1 + L * R) ≤ (b : ℝ) - a :=
    herr.trans (hsize'.trans hrel)
  have hbracket : (T : ℝ) + 2 * n * (((b : ℝ) - a) / L + N * (L⁻¹ + R)) ≤
      (2 * n + 1) * ((b : ℝ) - a) / L := by
    apply (le_div_iff₀ hL).mpr
    have hident : ((T : ℝ) + 2 * n * (((b : ℝ) - a) / L + N * (L⁻¹ + R))) * L =
        2 * n * ((b : ℝ) - a) + ((T : ℝ) * L + 2 * n * N * (1 + L * R)) := by
      field_simp
      ring
    rw [hident]
    nlinarith only [herr']
  have hlog : Real.log b ≤ ((12 * (k + 1) + 2 : ℕ) : ℝ) * L := by
    have ht := Real.log_le_log (show 0 < (b : ℝ) by linarith)
      (show (b : ℝ) ≤ ((z : ℝ) + 1) ^ (12 * (k + 1) + 2) by exact_mod_cast hroot'.le)
    rwa [Real.log_pow] at ht
  have hy : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hratio : (2 * n + 1) * ((b : ℝ) - a) / L ≤
      ((12 * (k + 1) + 2 : ℕ) : ℝ) * (2 * n + 1) * (((b : ℝ) - a) / Real.log b) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hL hlogb).mpr
    have ht := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (2 * n + 1) * ((b : ℝ) - a) by positivity)
    nlinarith only [ht]
  calc
    _ ≤ E * ((T : ℝ) + 2 * n * (((b : ℝ) - a) / L + N * (L⁻¹ + R))) :=
      primePenalty_pow_interval_finite g hg k a b H z hab hH hz1 hzb hTb
    _ ≤ E * ((2 * n + 1) * ((b : ℝ) - a) / L) := mul_le_mul_of_nonneg_left hbracket hE
    _ ≤ E * (((12 * (k + 1) + 2 : ℕ) : ℝ) * (2 * n + 1) * (((b : ℝ) - a) / Real.log b)) :=
      mul_le_mul_of_nonneg_left hratio hE
    _ = _ := by dsimp [n, E]; ring

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

 

theorem primePenalty_pow_interval_uniform (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ B : ℕ, ∀ (g : ℕ → ℝ), (∀ p, 0 ≤ g p ∧ g p ≤ 1) →
      ∀ a b : ℕ, B ≤ b → a ≤ b → η * b ≤ (b : ℝ) - a →
      (∑ m ∈ Finset.Ioc a b, ((primePenalty g) ^ (k + 1)) m) ≤
        ((12 * (k + 1) + 2 : ℕ) : ℝ) * (2 * ((k + 1 : ℕ) : ℝ) + 1) *
          (((b : ℝ) - a) / Real.log b) * (penaltyEuler g b) ^ (k + 1) := by
  obtain ⟨Z, hZ⟩ := exists_nat_ge ((1 + 10 * ((k + 1 : ℕ) : ℝ)) / η)
  let W := max 2 Z
  let r := 12 * (k + 1) + 2
  have hr : r ≠ 0 := by omega
  refine ⟨W ^ r, ?_⟩
  intro g hg a b hb hab hrel
  let z := Nat.nthRoot r b
  have hW : W ≤ z := (Nat.le_nthRoot_iff hr).mpr hb
  have hz : 2 ≤ z := (le_max_left 2 Z).trans hW
  have hZz : (Z : ℝ) ≤ z := by exact_mod_cast (le_max_right 2 Z).trans hW
  have hsize : 1 + 10 * ((k + 1 : ℕ) : ℝ) ≤ η * z := by
    have ht := (div_le_iff₀ hη).mp (hZ.trans hZz)
    linarith
  exact primePenalty_pow_interval_at_level g hg k a b z η hab hz hη hrel hsize
    (Nat.pow_nthRoot_le (.inl hr)) (Nat.lt_pow_nthRoot_add_one hr b)

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

lemma reciprocal_gap_sum (b : ℕ) (hb : 1 ≤ b) :
    (∑ p ∈ Finset.Icc 2 b, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))) =
      1 - 1 / (b : ℝ) := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ b hb ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    ring

lemma prime_reciprocal_gap_le_one (b : ℕ) :
    (∑ p ∈ smallPrimes b, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))) ≤ 1 := by
  by_cases hb : b = 0
  · simp [hb, smallPrimes]
  have hsub : smallPrimes b ⊆ Finset.Icc 2 b := by
    intro p hp
    obtain ⟨hp, hpr⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨hpr.two_le, (Finset.mem_Icc.mp hp).2⟩
  calc
    _ ≤ ∑ p ∈ Finset.Icc 2 b, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      have hp1 : 1 < (p : ℝ) := by exact_mod_cast (show 1 < p from (Finset.mem_Icc.mp hp).1)
      apply sub_nonneg.mpr
      exact div_le_div_of_nonneg_left zero_le_one (by linarith) (by linarith)
    _ = 1 - 1 / (b : ℝ) := reciprocal_gap_sum b (by omega)
    _ ≤ 1 := by
      have hb0 : 0 ≤ (1 : ℝ) / (b : ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg b)
      linarith only [hb0]

lemma penaltyEuler_le_exp (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (b : ℕ) :
    penaltyEuler g b ≤ Real.exp (1 + ∑ p ∈ smallPrimes b, g p / p) := by
  have hsum : (∑ p ∈ smallPrimes b, g p / ((p : ℝ) - 1)) ≤
      1 + ∑ p ∈ smallPrimes b, g p / p := by
    calc
      _ ≤ ∑ p ∈ smallPrimes b, (g p / p + (1 / ((p : ℝ)-1) - 1 / p)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
        have hi : 0 ≤ 1 / ((p : ℝ) - 1) - 1 / (p : ℝ) :=
          sub_nonneg.mpr (div_le_div_of_nonneg_left zero_le_one (by linarith) (by linarith))
        have ht := mul_le_mul_of_nonneg_right (hg p).2 hi
        simp only [div_eq_mul_inv] at ht ⊢
        nlinarith only [ht]
      _ = (∑ p ∈ smallPrimes b, g p / p) +
          (∑ p ∈ smallPrimes b, (1 / ((p : ℝ)-1) - 1 / p)) := Finset.sum_add_distrib
      _ ≤ _ := by linarith only [prime_reciprocal_gap_le_one b]
  calc
    _ ≤ ∏ p ∈ smallPrimes b, Real.exp (g p / ((p : ℝ) - 1)) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
        exact add_nonneg zero_le_one (div_nonneg (hg p).1 (by linarith))
      · intro p _
        simpa only [add_comm] using Real.add_one_le_exp (g p / ((p : ℝ) - 1))
    _ = Real.exp (∑ p ∈ smallPrimes b, g p / ((p : ℝ) - 1)) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hsum

lemma penaltyEuler_pow_le_exp (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (b n : ℕ) :
    (penaltyEuler g b)^n ≤ Real.exp n * Real.exp (∑ p ∈ smallPrimes b, (n : ℝ) * g p / p) := by
  have hE : 0 ≤ penaltyEuler g b := zero_le_one.trans (penaltyEuler_one_le g (fun p => (hg p).1) b)
  calc
    _ ≤ (Real.exp (1 + ∑ p ∈ smallPrimes b, g p / p))^n :=
      pow_le_pow_left₀ hE (penaltyEuler_le_exp g hg b) n
    _ = Real.exp ((n : ℝ) * (1 + ∑ p ∈ smallPrimes b, g p / p)) := (Real.exp_nat_mul _ n).symm
    _ = _ := by
      rw [mul_add, mul_one, Real.exp_add, Finset.mul_sum]
      congr 2
      apply Finset.sum_congr rfl
      intro p _
      ring

 

theorem primePenalty_pow_relative_interval (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ B : ℕ, ∀ (g : ℕ → ℝ), (∀ p, 0 ≤ g p ∧ g p ≤ 1) →
      ∀ a b : ℕ, B ≤ b → a ≤ b → η * b ≤ (b : ℝ) - a →
      (∑ m ∈ Finset.Ioc a b, ((primePenalty g) ^ (k + 1)) m) ≤
        (((12 * (k + 1) + 2 : ℕ) : ℝ) * (2 * ((k + 1 : ℕ) : ℝ) + 1) * Real.exp (k+1)) *
          (((b : ℝ) - a) / Real.log b) *
            Real.exp (∑ p ∈ smallPrimes b, ((k + 1 : ℕ) : ℝ) * g p / p) := by
  obtain ⟨B, hB⟩ := primePenalty_pow_interval_uniform k η hη
  refine ⟨B, ?_⟩
  intro g hg a b hb hab hrel
  apply (hB g hg a b hb hab hrel).trans
  have hlog : 0 ≤ Real.log (b : ℝ) := by
    by_cases hb0 : b = 0
    · simp [hb0]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ b by omega))
  have hy : 0 ≤ (b : ℝ)-a := sub_nonneg.mpr (by exact_mod_cast hab)
  have ht := mul_le_mul_of_nonneg_left (penaltyEuler_pow_le_exp g hg b (k+1))
    (show 0 ≤ ((12 * (k+1)+2 : ℕ) : ℝ) * (2*((k+1 : ℕ):ℝ)+1) * (((b : ℝ)-a)/Real.log b) by positivity)
  convert ht using 1
  push_cast
  ring

end PrimeDegreePackets.Sieve
end
end

end OAI
