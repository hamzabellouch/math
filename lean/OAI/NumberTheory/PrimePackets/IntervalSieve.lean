import Mathlib
import OAI.NumberTheory.PrimePackets.PowerfulIdeals

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
namespace PrimeDegreePackets.Sieve
open Finset Nat ArithmeticFunction BoundingSieve

 
def reciprocalDensity : ArithmeticFunction ℝ := ⟨fun d => (d : ℝ)⁻¹, by simp⟩

lemma reciprocalDensity_multiplicative : reciprocalDensity.IsMultiplicative := by
  constructor
  · simp [reciprocalDensity]
  · intro a b _
    simp [reciprocalDensity, Nat.cast_mul, mul_comm]

 
def intervalSieve (a b P : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := Finset.Ioc a b
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := (b : ℝ) - a
  nu := reciprocalDensity
  nu_mult := reciprocalDensity_multiplicative
  nu_pos_of_prime := by
    intro p hp _
    exact inv_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

lemma interval_divisibility_card (a b d : ℕ) (hab : a ≤ b) :
    ((Finset.Ioc a b).filter (fun n => d ∣ n)).card = b / d - a / d := by
  have hdis : Disjoint ((Finset.Ioc 0 a).filter (fun n => d ∣ n))
      ((Finset.Ioc a b).filter (fun n => d ∣ n)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    simp only [mem_filter, Finset.mem_Ioc] at hn hm
    omega
  have hu : ((Finset.Ioc 0 a).filter (fun n => d ∣ n)) ∪
      ((Finset.Ioc a b).filter (fun n => d ∣ n)) =
      ((Finset.Ioc 0 b).filter (fun n => d ∣ n)) := by
    ext n
    simp only [Finset.mem_union, mem_filter, Finset.mem_Ioc]
    omega
  have H := congrArg Finset.card hu
  rw [Finset.card_union_of_disjoint hdis, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div] at H
  omega

lemma interval_multSum (a b P : ℕ) (hP : Squarefree P) (hab : a ≤ b) (d : ℕ) :
    (intervalSieve a b P hP).multSum d = (b / d : ℕ) - (a / d : ℕ) := by
  rw [BoundingSieve.multSum]
  change (∑ n ∈ Finset.Ioc a b, if d ∣ n then (1 : ℝ) else 0) = _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, interval_divisibility_card a b d hab]
  exact Nat.cast_sub (Nat.div_le_div_right hab)

lemma real_div_lt_nat_div_add_one (a : ℕ) {d : ℕ} (hd : 0 < d) :
    (a : ℝ) / d < (a / d : ℕ) + 1 := by
  have H : a < (a / d + 1) * d := by simpa [Nat.mul_comm] using Nat.lt_mul_div_succ a hd
  exact (div_lt_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr (by exact_mod_cast H)

lemma interval_rem_abs_le_one (a b P : ℕ) (hP : Squarefree P) (hab : a ≤ b)
    {d : ℕ} (hd : 0 < d) : |(intervalSieve a b P hP).rem d| ≤ 1 := by
  rw [BoundingSieve.rem, interval_multSum a b P hP hab]
  change |(b / d : ℕ) - (a / d : ℕ) - (d : ℝ)⁻¹ * ((b : ℝ) - a)| ≤ 1
  rw [abs_le]
  have ha := real_div_lt_nat_div_add_one a hd
  have hb := real_div_lt_nat_div_add_one b hd
  have ha' : ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / d := Nat.cast_div_le
  have hb' : ((b / d : ℕ) : ℝ) ≤ (b : ℝ) / d := Nat.cast_div_le
  simp only [div_eq_mul_inv] at *
  constructor <;> nlinarith

lemma interval_selbergTerms (a b P : ℕ) (hP : Squarefree P) (d : ℕ) :
    (intervalSieve a b P hP).selbergTerms d = (d.totient : ℝ)⁻¹ := by
  rw [BoundingSieve.selbergTerms_apply]
  have ht : (d.totient : ℝ) = (d : ℝ) * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have H := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors d)
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
      Rat.cast_one, Rat.cast_inv] using H
  simp only [intervalSieve, reciprocalDensity, ArithmeticFunction.coe_mk, ht,
    mul_inv, Finset.prod_inv_distrib]

 

theorem sifted_interval_bound (a b P z : ℕ) (hP : Squarefree P) (hab : a ≤ b)
    (hz : 1 ≤ z) (hprimes : ∀ p : ℕ, p.Prime → p ≤ z → p ∣ P) :
    (((Finset.Ioc a b).filter (fun n => P.Coprime n)).card : ℝ) ≤
      ((b : ℝ) - a) / Real.log (z + 1) + ((z : ℝ) * (z + 1))^2 := by
  let s := intervalSieve a b P hP
  have hs := optimized_sieve_bound s hz
  have he := optimalWeight_errSum_le s hz (by norm_num : (0 : ℝ) ≤ 1)
    (fun d hd => interval_rem_abs_le_one a b P hP hab
      (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP.ne_zero (Nat.dvd_of_mem_divisors hd))))
  have hlog : 0 < Real.log (z + 1) := Real.log_pos (by exact_mod_cast (by omega : 1 < z + 1))
  have hden : Real.log (z + 1) ≤ sieveDenominator s z := by
    apply (show Real.log (z + 1) ≤ (harmonic z : ℝ) by
      simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic z).trans
    apply (harmonic_le_inverse_totient_sum hP.ne_zero hprimes).trans
    unfold sieveDenominator
    simp only [s, interval_selbergTerms]
    exact le_rfl
  have herr : (∑ d ∈ s.prodPrimes.divisors, if d ≤ z then (s.nu d)⁻¹ else 0) ≤
      (z : ℝ) * (z + 1) := by
    change (∑ d ∈ P.divisors, if d ≤ z then ((d : ℝ)⁻¹)⁻¹ else 0) ≤ _
    simp only [inv_inv]
    rw [← Finset.sum_filter]
    calc
      _ ≤ ∑ d ∈ P.divisors.filter (fun d => d ≤ z), (z : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact_mod_cast (Finset.mem_filter.mp hd).2
      _ ≤ ∑ _d ∈ Finset.range (z + 1), (z : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (by intros; positivity)
        intro d hd
        exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hd).2; omega)
      _ = _ := by simp; ring
  have herr0 : 0 ≤ ∑ d ∈ s.prodPrimes.divisors, if d ≤ z then (s.nu d)⁻¹ else 0 := by
    apply Finset.sum_nonneg
    intro d hd
    split_ifs
    · exact inv_nonneg.mpr (s.nu_pos_of_dvd_prodPrimes (Nat.dvd_of_mem_divisors hd)).le
    · rfl
  have hm : 0 ≤ (b : ℝ) - a := by exact sub_nonneg.mpr (by exact_mod_cast hab)
  have hf : s.siftedSum = (((Finset.Ioc a b).filter (fun n => P.Coprime n)).card : ℝ) := by
    simp [BoundingSieve.siftedSum, s, intervalSieve]
  rw [hf] at hs
  apply hs.trans
  apply _root_.add_le_add
  · exact div_le_div_of_nonneg_left hm hlog hden
  · apply he.trans
    rw [one_mul]
    exact pow_le_pow_left₀ herr0 herr 2

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

 
def truncatedTotientSum (P z : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, if d ≤ z then (d.totient : ℝ)⁻¹ else 0

lemma sum_divisors_coprime {P R : ℕ} (h : P.Coprime R) (f : ℕ → ℝ) :
    (∑ d ∈ (P * R).divisors, f d) =
      ∑ d ∈ P.divisors, ∑ e ∈ R.divisors, f (d * e) := by
  rw [h.divisors_mul, Finset.sum_map]
  change (∑ x ∈ (P.divisors ×ˢ R.divisors).attach, f (x.val.1 * x.val.2)) = _
  rw [Finset.sum_attach _ (fun x : ℕ × ℕ => f (x.1 * x.2)), Finset.sum_product]

lemma truncatedTotientSum_mul_le {P R z : ℕ} (h : P.Coprime R) :
    truncatedTotientSum (P * R) z ≤
      truncatedTotientSum P z * ∑ e ∈ R.divisors, (e.totient : ℝ)⁻¹ := by
  rw [truncatedTotientSum, sum_divisors_coprime h]
  unfold truncatedTotientSum
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have hde : d.Coprime e :=
    (h.of_dvd_left (Nat.dvd_of_mem_divisors hd)).of_dvd_right (Nat.dvd_of_mem_divisors he)
  have he1 : 1 ≤ e := Nat.pos_of_mem_divisors he
  by_cases hdz : d * e ≤ z
  · have hd_le : d ≤ z := (Nat.le_mul_of_pos_right d he1).trans hdz
    simp only [ite_eq_left hdz, ite_eq_left hd_le, Nat.totient_mul hde, Nat.cast_mul, mul_inv, le_refl]
  · rw [ite_eq_right hdz]
    split_ifs <;> positivity

lemma fullTotientSum_pos {P : ℕ} (hP : P ≠ 0) :
    0 < ∑ d ∈ P.divisors, (d.totient : ℝ)⁻¹ := by
  apply Finset.sum_pos'
  · intro d _
    positivity
  · exact ⟨1, Nat.one_mem_divisors.mpr hP, by simp⟩

lemma harmonic_le_truncatedTotientSum_mul {P R z : ℕ} (h : P.Coprime R)
    (hPR : P * R ≠ 0) (hprimes : ∀ p : ℕ, p.Prime → p ≤ z → p ∣ P * R) :
    (harmonic z : ℝ) ≤
      truncatedTotientSum P z * ∑ e ∈ R.divisors, (e.totient : ℝ)⁻¹ := by
  exact (harmonic_le_inverse_totient_sum hPR hprimes).trans
    (truncatedTotientSum_mul_le h)

 

theorem sifted_interval_complement_bound (a b P R z : ℕ)
    (hP : Squarefree P) (hR : R ≠ 0) (hPR : P.Coprime R) (hab : a ≤ b)
    (hz : 1 ≤ z) (hprimes : ∀ p : ℕ, p.Prime → p ≤ z → p ∣ P * R) :
    (((Finset.Ioc a b).filter (fun n => P.Coprime n)).card : ℝ) ≤
      (((b : ℝ) - a) / Real.log (z + 1)) *
        (∑ e ∈ R.divisors, (e.totient : ℝ)⁻¹) +
        ((z : ℝ) * (z + 1)) ^ 2 := by
  let s := intervalSieve a b P hP
  have hs := optimized_sieve_bound s hz
  have he := optimalWeight_errSum_le s hz (by norm_num : (0 : ℝ) ≤ 1)
    (fun d hd => interval_rem_abs_le_one a b P hP hab
      (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP.ne_zero (Nat.dvd_of_mem_divisors hd))))
  have hlog : 0 < Real.log (z + 1) := Real.log_pos (by exact_mod_cast (by omega : 1 < z + 1))
  have hden : Real.log (z + 1) ≤ sieveDenominator s z *
      (∑ e ∈ R.divisors, (e.totient : ℝ)⁻¹) := by
    apply (show Real.log (z + 1) ≤ (harmonic z : ℝ) by
      simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic z).trans
    have H := harmonic_le_truncatedTotientSum_mul hPR (mul_ne_zero hP.ne_zero hR) hprimes
    unfold sieveDenominator
    change (harmonic z : ℝ) ≤ (∑ d ∈ P.divisors,
      if d ≤ z then (intervalSieve a b P hP).selbergTerms d else 0) * _
    simpa only [interval_selbergTerms, truncatedTotientSum] using H
  have herr : (∑ d ∈ s.prodPrimes.divisors, if d ≤ z then (s.nu d)⁻¹ else 0) ≤
      (z : ℝ) * (z + 1) := by
    change (∑ d ∈ P.divisors, if d ≤ z then ((d : ℝ)⁻¹)⁻¹ else 0) ≤ _
    simp only [inv_inv]
    rw [← Finset.sum_filter]
    calc
      _ ≤ ∑ d ∈ P.divisors.filter (fun d => d ≤ z), (z : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact_mod_cast (Finset.mem_filter.mp hd).2
      _ ≤ ∑ _d ∈ Finset.range (z + 1), (z : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (by intros; positivity)
        intro d hd
        exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hd).2; omega)
      _ = _ := by simp; ring
  have herr0 : 0 ≤ ∑ d ∈ s.prodPrimes.divisors, if d ≤ z then (s.nu d)⁻¹ else 0 := by
    apply Finset.sum_nonneg
    intro d hd
    split_ifs
    · exact inv_nonneg.mpr (s.nu_pos_of_dvd_prodPrimes (Nat.dvd_of_mem_divisors hd)).le
    · rfl
  have hm : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hf : s.siftedSum = (((Finset.Ioc a b).filter (fun n => P.Coprime n)).card : ℝ) := by
    simp [BoundingSieve.siftedSum, s, intervalSieve]
  rw [hf] at hs
  apply hs.trans
  apply _root_.add_le_add
  · change ((b : ℝ) - a) / sieveDenominator s z ≤ _
    have hD := sieveDenominator_pos s hz
    apply (div_le_iff₀ hD).mpr
    have H := mul_le_mul_of_nonneg_left hden hm
    have H' := (le_div_iff₀ hlog).mpr H
    convert H' using 1; ring
  · apply he.trans
    rw [one_mul]
    exact pow_le_pow_left₀ herr0 herr 2

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

lemma squarefree_prime_product (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    (fun p hp => (hS p hp).squarefree)
  simpa only [← Nat.coprime_iff_isRelPrime] using
    (Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq

lemma fullTotientSum_mul {P R : ℕ} (h : P.Coprime R) :
    (∑ d ∈ (P * R).divisors, (d.totient : ℝ)⁻¹) =
      (∑ d ∈ P.divisors, (d.totient : ℝ)⁻¹) *
      (∑ e ∈ R.divisors, (e.totient : ℝ)⁻¹) := by
  rw [sum_divisors_coprime h, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hde : d.Coprime e :=
    (h.of_dvd_left (Nat.dvd_of_mem_divisors hd)).of_dvd_right (Nat.dvd_of_mem_divisors he)
  rw [Nat.totient_mul hde, Nat.cast_mul, mul_inv]

lemma fullTotientSum_prime_product (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ d ∈ (∏ p ∈ S, p).divisors, (d.totient : ℝ)⁻¹) =
      ∏ p ∈ S, (1 + ((p : ℝ) - 1)⁻¹) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hpP := hS p (Finset.mem_insert_self _ _)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hc : p.Coprime (∏ q ∈ S, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (Nat.coprime_primes hpP (hS' q hq)).mpr (by intro h; exact hp (h ▸ hq))
    rw [Finset.prod_insert hp, fullTotientSum_mul hc, ih hS', Finset.prod_insert hp]
    congr 1
    simp [hpP.divisors, hpP.ne_one.symm, Nat.totient_prime hpP, Nat.cast_sub hpP.one_le]

 

def mixtureMass (S T : Finset ℕ) (g : ℕ → ℝ) : ℝ :=
  (∏ p ∈ T, (1 - g p)) * ∏ p ∈ S \ T, g p

def softWeight (S : Finset ℕ) (g : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∏ p ∈ S, ((1 - g p) * (if p.Coprime m then 1 else 0) + g p)

lemma mixtureMass_nonneg (S T : Finset ℕ) (g : ℕ → ℝ)
    (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) : 0 ≤ mixtureMass S T g := by
  exact mul_nonneg (Finset.prod_nonneg (fun p _ => sub_nonneg.mpr (hg p).2))
    (Finset.prod_nonneg (fun p _ => (hg p).1))

lemma sum_mixtureMass (S : Finset ℕ) (g : ℕ → ℝ) :
    ∑ T ∈ S.powerset, mixtureMass S T g = 1 := by
  unfold mixtureMass
  rw [← Finset.prod_add]
  simp

lemma coprime_prime_product_indicator (T : Finset ℕ) (m : ℕ) :
    (if (∏ p ∈ T, p).Coprime m then (1 : ℝ) else 0) =
      ∏ p ∈ T, (if p.Coprime m then (1 : ℝ) else 0) := by
  simp only [Finset.prod_boole, Nat.coprime_prod_left_iff]

lemma softWeight_eq_mixture (S : Finset ℕ) (g : ℕ → ℝ) (m : ℕ) :
    softWeight S g m = ∑ T ∈ S.powerset,
      mixtureMass S T g * (if (∏ p ∈ T, p).Coprime m then 1 else 0) := by
  rw [softWeight, Finset.prod_add]
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.prod_mul_distrib, coprime_prime_product_indicator, mixtureMass]
  ring

lemma sum_softWeight_eq_mixture (S : Finset ℕ) (g : ℕ → ℝ) (a b : ℕ) :
    (∑ m ∈ Finset.Ioc a b, softWeight S g m) =
      ∑ T ∈ S.powerset, mixtureMass S T g *
        (((Finset.Ioc a b).filter (fun m => (∏ p ∈ T, p).Coprime m)).card : ℝ) := by
  simp_rw [softWeight_eq_mixture]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  rw [← Finset.mul_sum]
  congr 1
  simp

lemma sum_mixture_complementEuler (S : Finset ℕ) (g : ℕ → ℝ) :
    (∑ T ∈ S.powerset, mixtureMass S T g *
      ∏ p ∈ S \ T, (1 + ((p : ℝ) - 1)⁻¹)) =
      ∏ p ∈ S, (1 + g p / ((p : ℝ) - 1)) := by
  calc
    _ = ∑ T ∈ S.powerset, (∏ p ∈ T, (1 - g p)) *
        ∏ p ∈ S \ T, (g p * (1 + ((p : ℝ) - 1)⁻¹)) := by
      apply Finset.sum_congr rfl
      intro T _
      rw [mixtureMass, Finset.prod_mul_distrib]
      ring
    _ = ∏ p ∈ S, ((1 - g p) + g p * (1 + ((p : ℝ) - 1)⁻¹)) :=
      (Finset.prod_add _ _ _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p _
      ring

 

theorem soft_interval_bound (a b z : ℕ) (S : Finset ℕ) (g : ℕ → ℝ)
    (hab : a ≤ b) (hz : 1 ≤ z) (hS : ∀ p ∈ S, p.Prime)
    (hcontains : ∀ p : ℕ, p.Prime → p ≤ z → p ∈ S)
    (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) :
    (∑ m ∈ Finset.Ioc a b, softWeight S g m) ≤
      (((b : ℝ) - a) / Real.log (z + 1)) *
        (∏ p ∈ S, (1 + g p / ((p : ℝ) - 1))) +
        ((z : ℝ) * (z + 1)) ^ 2 := by
  rw [sum_softWeight_eq_mixture]
  calc
    _ ≤ ∑ T ∈ S.powerset, mixtureMass S T g *
        ((((b : ℝ) - a) / Real.log (z + 1)) *
          (∏ p ∈ S \ T, (1 + ((p : ℝ) - 1)⁻¹)) +
          ((z : ℝ) * (z + 1)) ^ 2) := by
      apply Finset.sum_le_sum
      intro T hT
      have hTS := Finset.mem_powerset.mp hT
      have heq : (∏ p ∈ T, p) * (∏ p ∈ S \ T, p) = ∏ p ∈ S, p :=
        by rw [mul_comm, Finset.prod_sdiff hTS]
      have hsf : Squarefree ((∏ p ∈ T, p) * (∏ p ∈ S \ T, p)) :=
        heq ▸ squarefree_prime_product S hS
      obtain ⟨hcop, hsT, hsR⟩ := Nat.squarefree_mul_iff.mp hsf
      apply mul_le_mul_of_nonneg_left _ (mixtureMass_nonneg S T g hg)
      have H := sifted_interval_complement_bound a b _ _ z hsT hsR.ne_zero hcop hab hz (by
        intro p hp hpz
        rw [heq]
        exact Finset.dvd_prod_of_mem (fun q : ℕ => q) (hcontains p hp hpz))
      simpa only [fullTotientSum_prime_product _ (fun p hp => hS p (Finset.mem_sdiff.mp hp).1)] using H
    _ = _ := by
      rw [show (∑ T ∈ S.powerset, mixtureMass S T g *
          ((((b : ℝ) - a) / Real.log (z + 1)) *
            (∏ p ∈ S \ T, (1 + ((p : ℝ) - 1)⁻¹)) +
            ((z : ℝ) * (z + 1)) ^ 2)) =
          (((b : ℝ) - a) / Real.log (z + 1)) *
            (∑ T ∈ S.powerset, mixtureMass S T g *
              (∏ p ∈ S \ T, (1 + ((p : ℝ) - 1)⁻¹))) +
          (∑ T ∈ S.powerset, mixtureMass S T g) *
            ((z : ℝ) * (z + 1)) ^ 2 by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro T _
        ring]
      rw [sum_mixtureMass, one_mul, sum_mixture_complementEuler]

end PrimeDegreePackets.Sieve

open scoped BigOperators
namespace PrimeDegreePackets.Sieve

 
def primePenalty (g : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => if m = 0 then 0 else ∏ p ∈ m.primeFactors, g p, by simp⟩

lemma primePenalty_apply (g : ℕ → ℝ) {m : ℕ} (hm : m ≠ 0) :
    primePenalty g m = ∏ p ∈ m.primeFactors, g p := by
  simp [primePenalty, hm]

lemma primePenalty_multiplicative (g : ℕ → ℝ) :
    (primePenalty g).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [primePenalty], ?_⟩
  intro m n hm hn hmn
  simp only [primePenalty_apply g hm, primePenalty_apply g hn,
    primePenalty_apply g (mul_ne_zero hm hn), Nat.primeFactors_mul hm hn]
  exact Finset.prod_union hmn.disjoint_primeFactors

lemma primePenalty_one (g : ℕ → ℝ) : primePenalty g 1 = 1 :=
  (primePenalty_multiplicative g).map_one

lemma primePenalty_prime_pow (g : ℕ → ℝ) {p j : ℕ} (hp : p.Prime) (hj : j ≠ 0) :
    primePenalty g (p ^ j) = g p := by
  rw [primePenalty_apply _ (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_pow _ hj,
    hp.primeFactors, Finset.prod_singleton]

lemma primePenalty_nonneg (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p) (m : ℕ) :
    0 ≤ primePenalty g m := by
  by_cases hm : m = 0
  · simp [hm]
  · rw [primePenalty_apply _ hm]
    exact Finset.prod_nonneg (fun p _ => hg p)

lemma primePenalty_le_one (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (m : ℕ) :
    primePenalty g m ≤ 1 := by
  by_cases hm : m = 0
  · simp [hm]
  · rw [primePenalty_apply _ hm]
    exact Finset.prod_le_one₀ (fun prime _ => (hg prime).1) (fun prime _ => (hg prime).2)

 

def logWeight (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => Real.log m * f m, by simp⟩

@[simp] lemma logWeight_apply (f : ArithmeticFunction ℝ) (m : ℕ) :
    logWeight f m = Real.log m * f m := rfl

lemma logWeight_mul (f g : ArithmeticFunction ℝ) :
    logWeight (f * g) = f * logWeight g + g * logWeight f := by
  rw [mul_comm g (logWeight f)]
  ext m
  rw [ArithmeticFunction.add_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply, logWeight_apply, ArithmeticFunction.mul_apply,
    Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  rintro ⟨d, e⟩ hde
  obtain ⟨hde, hm⟩ := Nat.mem_divisorsAntidiagonal.mp hde
  have hd : d ≠ 0 := by intro hd; simp_all
  have he : e ≠ 0 := by intro he; simp_all
  rw [← hde, Nat.cast_mul, Real.log_mul (by exact_mod_cast hd) (by exact_mod_cast he)]
  simp only [logWeight_apply]
  ring

 
def coefficientLogDerivation : Derivation ℝ (ArithmeticFunction ℝ) (ArithmeticFunction ℝ) where
  toFun := logWeight
  map_add' f g := by ext m; simp [mul_add]
  map_smul' r f := by ext m; simp [mul_left_comm]
  map_one_eq_zero' := by
    ext m
    by_cases hm : m = 1 <;> simp [hm]
  leibniz' f g := by
    change logWeight (f * g) = f * logWeight g + g * logWeight f
    exact logWeight_mul f g

lemma logWeight_pow (f : ArithmeticFunction ℝ) (k : ℕ) :
    logWeight (f ^ (k + 1)) = ((k + 1 : ℕ) : ℝ) • (f ^ k * logWeight f) := by
  have H := coefficientLogDerivation.leibniz_pow f (k + 1)
  change logWeight (f ^ (k + 1)) = (k + 1) • (f ^ (k + 1 - 1) * logWeight f) at H
  simpa only [Nat.add_sub_cancel, Nat.cast_smul_eq_nsmul] using H

 
lemma convolution_nonneg {f g : ArithmeticFunction ℝ}
    (hf : ∀ m, 0 ≤ f m) (hg : ∀ m, 0 ≤ g m) (m : ℕ) :
    0 ≤ (f * g) m := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg (fun de _ => mul_nonneg (hf de.1) (hg de.2))

lemma convolution_pow_nonneg {f : ArithmeticFunction ℝ} (hf : ∀ m, 0 ≤ f m)
    (k m : ℕ) : 0 ≤ (f ^ k) m := by
  induction k generalizing m with
  | zero => simp [ArithmeticFunction.one_apply]; split_ifs <;> positivity
  | succ k ih =>
    rw [pow_succ]
    exact convolution_nonneg ih hf m

 
def reciprocalCoefficients (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => f m / m, by simp⟩

@[simp] lemma reciprocalCoefficients_apply (f : ArithmeticFunction ℝ) (m : ℕ) :
    reciprocalCoefficients f m = f m / m := rfl

lemma reciprocalCoefficients_multiplicative {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) : (reciprocalCoefficients f).IsMultiplicative := by
  refine ⟨by simp [hf], ?_⟩
  intro m n hmn
  simp only [reciprocalCoefficients_apply, hf.map_mul_of_coprime hmn, Nat.cast_mul]
  ring

open scoped ArithmeticFunction.zeta

 
def divisorReciprocal (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  reciprocalCoefficients f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

lemma divisorReciprocal_apply (f : ArithmeticFunction ℝ) (m : ℕ) :
    divisorReciprocal f m = ∑ d ∈ m.divisors, f d / d := by
  rw [divisorReciprocal, ArithmeticFunction.coe_mul_zeta_apply]
  rfl

lemma divisorReciprocal_multiplicative {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) : (divisorReciprocal f).IsMultiplicative :=
  (reciprocalCoefficients_multiplicative hf).mul
    ArithmeticFunction.isMultiplicative_zeta.natCast

lemma divisorReciprocal_nonneg {f : ArithmeticFunction ℝ}
    (hf : ∀ m, 0 ≤ f m) (m : ℕ) : 0 ≤ divisorReciprocal f m := by
  rw [divisorReciprocal_apply]
  exact Finset.sum_nonneg (fun d _ => div_nonneg (hf d) (Nat.cast_nonneg d))

lemma geometric_partial_sum_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    ∑ j ∈ Finset.range k, r ^ j ≤ (1 - r)⁻¹ := by
  rw [inv_eq_one_div, le_div_iff₀ (by linarith : 0 < 1 - r), geom_sum_mul_neg]
  exact sub_le_self _ (pow_nonneg hr0 k)

lemma primePenalty_divisorReciprocal_pow (g : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    divisorReciprocal (primePenalty g) (p ^ k) =
      1 + g p * (p : ℝ)⁻¹ * ∑ j ∈ Finset.range k, ((p : ℝ)⁻¹) ^ j := by
  rw [divisorReciprocal_apply, Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ']
  simp only [pow_zero, primePenalty_one, Nat.cast_one, div_one]
  rw [add_comm, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [primePenalty_prime_pow g hp (by omega), Nat.cast_pow, pow_succ]
  ring

lemma primePenalty_divisorReciprocal_pow_le (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    divisorReciprocal (primePenalty g) (p ^ k) ≤ 1 + g p / ((p : ℝ) - 1) := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hr := geometric_partial_sum_le (p : ℝ)⁻¹ (by positivity)
    (inv_lt_one_of_one_lt₀ hp1) k
  rw [primePenalty_divisorReciprocal_pow g hp k]
  apply _root_.add_le_add (le_refl 1)
  calc
    _ ≤ g p * (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹)⁻¹ :=
      mul_le_mul_of_nonneg_left hr (mul_nonneg (hg p) (by positivity))
    _ = g p / ((p : ℝ) - 1) := by
      field_simp

 
lemma primePenalty_divisorReciprocal_le (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p)
    {m : ℕ} (hm : m ≠ 0) :
    divisorReciprocal (primePenalty g) m ≤
      ∏ p ∈ m.primeFactors, (1 + g p / ((p : ℝ) - 1)) := by
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
    (divisorReciprocal_multiplicative (primePenalty_multiplicative g)) hm]
  change (∏ p ∈ m.factorization.support,
    divisorReciprocal (primePenalty g) (p ^ m.factorization p)) ≤ _
  rw [Nat.support_factorization]
  apply Finset.prod_le_prod₀
  · intro p _
    exact divisorReciprocal_nonneg (primePenalty_nonneg g hg) _
  · intro p hp
    exact primePenalty_divisorReciprocal_pow_le g hg (Nat.prime_of_mem_primeFactors hp) _

 
lemma reciprocalCoefficients_mul (f g : ArithmeticFunction ℝ) :
    reciprocalCoefficients (f * g) = reciprocalCoefficients f * reciprocalCoefficients g := by
  ext m
  rw [reciprocalCoefficients_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  rintro ⟨d, e⟩ hde
  have hde := (Nat.mem_divisorsAntidiagonal.mp hde).1
  simp only [reciprocalCoefficients_apply]
  rw [← hde, Nat.cast_mul]
  ring

lemma divisorReciprocal_mono_divisor {f : ArithmeticFunction ℝ}
    (hf : ∀ m, 0 ≤ f m) {d m : ℕ} (hm : m ≠ 0) (hdm : d ∣ m) :
    divisorReciprocal f d ≤ divisorReciprocal f m := by
  simp only [divisorReciprocal_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hm hdm)
    (fun i _ _ => div_nonneg (hf i) (Nat.cast_nonneg i))

lemma divisorReciprocal_mul_le {f g : ArithmeticFunction ℝ}
    (hf : ∀ m, 0 ≤ f m) (hg : ∀ m, 0 ≤ g m) {m : ℕ} (hm : m ≠ 0) :
    divisorReciprocal (f * g) m ≤ divisorReciprocal f m * divisorReciprocal g m := by
  rw [divisorReciprocal, reciprocalCoefficients_mul, mul_assoc]
  change (reciprocalCoefficients f * divisorReciprocal g) m ≤ _
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun d e => reciprocalCoefficients f d * divisorReciprocal g e)]
  calc
    _ ≤ ∑ d ∈ m.divisors, (f d / d) * divisorReciprocal g m := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (divisorReciprocal_mono_divisor hg hm (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))
        (div_nonneg (hf d) (Nat.cast_nonneg d))
    _ = _ := by rw [← Finset.sum_mul, ← divisorReciprocal_apply]

lemma divisorReciprocal_one {m : ℕ} (hm : m ≠ 0) :
    divisorReciprocal (1 : ArithmeticFunction ℝ) m = 1 := by
  have hrec : reciprocalCoefficients (1 : ArithmeticFunction ℝ) = 1 := by
    ext d
    by_cases hd : d = 1 <;> simp [hd]
  rw [divisorReciprocal, hrec, one_mul]
  simp [hm]

lemma divisorReciprocal_pow_le {f : ArithmeticFunction ℝ}
    (hf : ∀ m, 0 ≤ f m) (k : ℕ) {m : ℕ} (hm : m ≠ 0) :
    divisorReciprocal (f ^ k) m ≤ (divisorReciprocal f m) ^ k := by
  induction k with
  | zero => simp [divisorReciprocal_one hm]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (divisorReciprocal_mul_le (convolution_pow_nonneg hf k) hf hm).trans
      (mul_le_mul_of_nonneg_right ih (divisorReciprocal_nonneg hf m))

lemma sum_reciprocal_le_divisorReciprocal_factorial {f : ArithmeticFunction ℝ}
    (hf : ∀ m, 0 ≤ f m) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, f m / m) ≤ divisorReciprocal f (N.factorial) := by
  rw [divisorReciprocal_apply]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial hm1 hmN, Nat.factorial_ne_zero N⟩
  · intro m _ _
    exact div_nonneg (hf m) (Nat.cast_nonneg m)

 
theorem sum_primePenalty_pow_reciprocal_le (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p)
    (k N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ((primePenalty g) ^ k) m / m) ≤
      (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (1 + g p / ((p : ℝ) - 1))) ^ k := by
  have hfactor : (N.factorial).primeFactors = (Finset.Icc 1 N).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primeFactors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hp, hpd, _⟩
      exact ⟨⟨hp.one_le, hp.dvd_factorial.mp hpd⟩, hp⟩
    · rintro ⟨⟨_, hpN⟩, hp⟩
      exact ⟨hp, hp.dvd_factorial.mpr hpN, Nat.factorial_ne_zero N⟩
  calc
    _ ≤ divisorReciprocal ((primePenalty g) ^ k) (N.factorial) :=
      sum_reciprocal_le_divisorReciprocal_factorial
        (convolution_pow_nonneg (primePenalty_nonneg g hg) k) N
    _ ≤ (divisorReciprocal (primePenalty g) (N.factorial)) ^ k :=
      divisorReciprocal_pow_le (primePenalty_nonneg g hg) k (Nat.factorial_ne_zero N)
    _ ≤ _ := by
      apply pow_le_pow_left₀ (divisorReciprocal_nonneg (primePenalty_nonneg g hg) _)
      rw [← hfactor]
      exact primePenalty_divisorReciprocal_le g hg (Nat.factorial_ne_zero N)

 
def largeFactorConvolution (f : ArithmeticFunction ℝ) (k H m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors.filter (H < ·), f d * (f ^ k) (m / d)

lemma largeFactorConvolution_nonneg {f : ArithmeticFunction ℝ}
    (hf : ∀ m, 0 ≤ f m) (k H m : ℕ) : 0 ≤ largeFactorConvolution f k H m := by
  exact Finset.sum_nonneg (fun d _ =>
    mul_nonneg (hf d) (convolution_pow_nonneg hf k (m / d)))

 

lemma convolution_pow_le_largeFactor {f : ArithmeticFunction ℝ}
    (hf : ∀ m, 0 ≤ f m) (k H m : ℕ) (hH : 1 ≤ H) (hm : 2 ≤ m)
    (hlog : 2 * ((k + 1 : ℕ) : ℝ) * Real.log H ≤ Real.log m) :
    (f ^ (k + 1)) m ≤ 2 * ((k + 1 : ℕ) : ℝ) * largeFactorConvolution f k H m := by
  have hH0 : 0 < (H : ℝ) := by exact_mod_cast hH
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hm1 : 1 < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hLH : 0 ≤ Real.log H := Real.log_nonneg (by exact_mod_cast hH)
  have hLm : 0 < Real.log m := Real.log_pos hm1
  have hk0 : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hcoef : 0 ≤ (f ^ (k + 1)) m := convolution_pow_nonneg hf _ _
  have hlarge : 0 ≤ largeFactorConvolution f k H m := largeFactorConvolution_nonneg hf _ _ _
  have hsum : (f ^ (k + 1)) m = ∑ d ∈ m.divisors, f d * (f ^ k) (m / d) := by
    rw [pow_succ, mul_comm, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun d e => f d * (f ^ k) e)]
  have hlogsum : Real.log m * (f ^ (k + 1)) m =
      ((k + 1 : ℕ) : ℝ) * ∑ d ∈ m.divisors,
        Real.log d * (f d * (f ^ k) (m / d)) := by
    have ht := congrArg (fun F : ArithmeticFunction ℝ => F m) (logWeight_pow f k)
    rw [mul_comm (f ^ k) (logWeight f)] at ht
    change Real.log m * (f ^ (k + 1)) m =
      ((k + 1 : ℕ) : ℝ) * (logWeight f * f ^ k) m at ht
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun d e => logWeight f d * (f ^ k) e)] at ht
    simpa only [logWeight_apply, mul_assoc] using ht
  have hbound : (∑ d ∈ m.divisors, Real.log d * (f d * (f ^ k) (m / d))) ≤
      Real.log H * (f ^ (k + 1)) m + Real.log m * largeFactorConvolution f k H m := by
    rw [hsum, largeFactorConvolution, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro d hd
    have hd0 : 0 < (d : ℝ) := by exact_mod_cast (Nat.pos_of_mem_divisors hd)
    have hterm : 0 ≤ f d * (f ^ k) (m / d) :=
      mul_nonneg (hf d) (convolution_pow_nonneg hf _ _)
    by_cases hHd : H < d
    · simp only [hHd, ite_true]
      have hdm : (d : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_dvd (by omega : 0 < m) (Nat.dvd_of_mem_divisors hd))
      exact (mul_le_mul_of_nonneg_right (Real.log_le_log hd0 hdm) hterm).trans
        (le_add_of_nonneg_left (mul_nonneg hLH hterm))
    · simp only [hHd, ite_false, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_right
        (Real.log_le_log hd0 (by exact_mod_cast (Nat.le_of_not_gt hHd))) hterm
  have hprod := mul_le_mul_of_nonneg_left hbound hk0.le
  rw [← hlogsum] at hprod
  have haux := mul_le_mul_of_nonneg_right hlog hcoef
  nlinarith

 

lemma sum_divisor_large_interval {A : Type*} [AddCommMonoid A]
    (F : ℕ → ℕ → A) (a b H : ℕ) :
    (∑ m ∈ Finset.Ioc a b, ∑ d ∈ m.divisors.filter (H < ·), F d (m / d)) =
      ∑ e ∈ Finset.Icc 1 (b / (H + 1)),
        ∑ d ∈ (Finset.Ioc (a / e) (b / e)).filter (H < ·), F d e := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun p _ => ⟨p.1 / p.2, p.2⟩)
  · intro p hp
    obtain ⟨hpm, hpd⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hdm, hHd⟩ := Finset.mem_filter.mp hpd
    obtain ⟨ham, hmb⟩ := Finset.mem_Ioc.mp hpm
    have hm0 : 0 < p.1 := by omega
    have hd0 := Nat.pos_of_mem_divisors hdm
    have hdvd := Nat.dvd_of_mem_divisors hdm
    have he0 : 0 < p.1 / p.2 := Nat.div_pos (Nat.le_of_dvd hm0 hdvd) hd0
    have hmul : p.2 * (p.1 / p.2) = p.1 := Nat.mul_div_cancel' hdvd
    apply Finset.mem_sigma.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      refine ⟨he0, (Nat.le_div_iff_mul_le (by omega : 0 < H + 1)).mpr ?_⟩
      calc
        (p.1 / p.2) * (H + 1) ≤ (p.1 / p.2) * p.2 := Nat.mul_le_mul_left _ (by omega)
        _ = p.1 := by simpa [mul_comm] using hmul
        _ ≤ b := hmb
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hHd⟩
      · exact (Nat.div_lt_iff_lt_mul he0).mpr (by simpa [hmul] using ham)
      · exact (Nat.le_div_iff_mul_le he0).mpr (by simpa [hmul] using hmb)
  · intro p hp q hq hpq
    obtain ⟨_, hpd⟩ := Finset.mem_sigma.mp hp
    obtain ⟨_, hqd⟩ := Finset.mem_sigma.mp hq
    have hd : p.2 = q.2 := by simpa using congrArg Sigma.snd hpq
    have he : p.1 / p.2 = q.1 / q.2 := congrArg Sigma.fst hpq
    have hm : p.1 = q.1 := by
      calc
        _ = p.2 * (p.1 / p.2) :=
          (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hpd).1)).symm
        _ = q.2 * (q.1 / q.2) := by rw [he, hd]
        _ = _ := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hqd).1)
    cases p
    cases q
    simp_all
  · intro q hq
    obtain ⟨hqe, hqd⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hqd, hHd⟩ := Finset.mem_filter.mp hqd
    have he0 : 0 < q.1 := (Finset.mem_Icc.mp hqe).1
    have hd0 : 0 < q.2 := by omega
    obtain ⟨had, hdb⟩ := Finset.mem_Ioc.mp hqd
    refine ⟨⟨q.2 * q.1, q.2⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul he0).mp had,
        (Nat.le_div_iff_mul_le he0).mp hdb⟩
    · exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨dvd_mul_right _ _, by positivity⟩, hHd⟩
    · simp [Nat.mul_div_cancel_left _ hd0]
  · intro p _
    rfl

lemma sum_largeFactorConvolution_le (f : ArithmeticFunction ℝ)
    (hf : ∀ m, 0 ≤ f m) (k a b H : ℕ) :
    (∑ m ∈ Finset.Ioc a b, largeFactorConvolution f k H m) ≤
      ∑ e ∈ Finset.Icc 1 (b / (H + 1)), (f ^ k) e *
        ∑ d ∈ Finset.Ioc (a / e) (b / e), f d := by
  simp only [largeFactorConvolution]
  rw [sum_divisor_large_interval (fun d e => f d * (f ^ k) e)]
  apply Finset.sum_le_sum
  intro e _
  rw [← Finset.sum_mul, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (convolution_pow_nonneg hf k e)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun d _ _ => hf d)

end PrimeDegreePackets.Sieve
end
end

end OAI
