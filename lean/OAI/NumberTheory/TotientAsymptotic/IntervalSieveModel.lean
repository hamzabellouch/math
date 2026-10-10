import OAI.NumberTheory.TotientAsymptotic.ShiftedSieveError

namespace OAI

/-! A concrete one-dimensional sieve for integers avoiding a prime interval. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

def intervalSievePrimes (S z : ℕ) : Finset ℕ :=
  (oddSievePrimes z).filter (fun p => S < p)

lemma mem_intervalSievePrimes {S z p : ℕ} :
    p ∈ intervalSievePrimes S z ↔ p ≤ z ∧ p.Prime ∧ p ≠ 2 ∧ S < p := by
  simp only [intervalSievePrimes,Finset.mem_filter,mem_oddSievePrimes,and_assoc]

lemma intervalSieve_prod_dvd (S z : ℕ) :
    (∏ p ∈ intervalSievePrimes S z,p) ∣ ∏ p ∈ oddSievePrimes z,p :=
  Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)

lemma intervalSieve_squarefree (S z : ℕ) :
    Squarefree (∏ p ∈ intervalSievePrimes S z,p) :=
  (oddSievePrimes_prod_squarefree z).squarefree_of_dvd (intervalSieve_prod_dvd S z)

def intervalSieveDensity : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => (p:ℝ)⁻¹)

lemma intervalSieveDensity_prime {p : ℕ} (hp : p.Prime) :
    intervalSieveDensity p = (p:ℝ)⁻¹ := by
  simp [intervalSieveDensity,ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero,hp.primeFactors]

lemma intervalSieveDensity_squarefree {d : ℕ} (hd : Squarefree d) :
    intervalSieveDensity d = (d:ℝ)⁻¹ := by
  rw [intervalSieveDensity,ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero,
    Finset.prod_inv_distrib,← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hd]

def intervalPrimeSieve (S X z : ℕ) (y : ℝ) (hy : 1 ≤ y) : SelbergSieve where
  support := Finset.Icc 1 X
  prodPrimes := ∏ p ∈ intervalSievePrimes S z,p
  prodPrimes_squarefree := intervalSieve_squarefree S z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := X
  nu := intervalSieveDensity
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := fun p hp _ => by
    rw [intervalSieveDensity_prime hp]
    exact inv_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := fun p hp _ => by
    rw [intervalSieveDensity_prime hp]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  level := y
  one_le_level := hy

lemma count_divisible_modulus {d : ℕ} (hd : 0 < d) :
    Nat.count (fun n => d ∣ n) d = 1 := by
  rw [Nat.count_eq_card_filter_range]
  have he : (Finset.range d).filter (fun n => d ∣ n) = {0} := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_singleton]
    constructor
    · rintro ⟨hn,hdn⟩
      by_contra hne
      exact (not_le_of_gt hn) (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdn)
    · rintro rfl
      exact ⟨hd,dvd_zero d⟩
  rw [he,Finset.card_singleton]

lemma intervalPrimeSieve_rem_le (S X z : ℕ) (y : ℝ) (hy : 1 ≤ y)
    {d : ℕ} (hd : Squarefree d) :
    |rem (s := (intervalPrimeSieve S X z y hy).toBoundingSieve) d| ≤ d+1 := by
  have hd0 := Nat.pos_of_ne_zero hd.ne_zero
  have hc := count_periodic_error d hd0 (fun n => d ∣ n)
    (fun n => by simp only [Nat.dvd_iff_mod_eq_zero,Nat.mod_mod]) X
  rw [count_divisible_modulus hd0] at hc
  norm_num only [Nat.cast_one,mul_one] at hc
  have hi := interval_count_discrepancy (fun n => d ∣ n) X
  have he : rem (s := (intervalPrimeSieve S X z y hy).toBoundingSieve) d =
      (((Finset.Icc 1 X).filter (fun n => d ∣ n)).card:ℝ)-(X:ℝ)/d := by
    simp only [rem,multSum,intervalPrimeSieve,Finset.sum_boole]
    rw [intervalSieveDensity_squarefree hd]
    ring
  rw [he]
  exact (abs_sub_le _ (Nat.count (fun n => d ∣ n) X:ℝ) _).trans
    ((add_le_add hi hc).trans_eq (by ring))

lemma intervalPrimeSieve_error_sum (S X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (∑ d ∈ (∏ p ∈ intervalSievePrimes S z,p).divisors,
      if (d:ℝ) ≤ y then (3:ℝ)^ArithmeticFunction.cardDistinctFactors d*
        |rem (s := (intervalPrimeSieve S X z y hy).toBoundingSieve) d| else 0) ≤ 2*y^3 := by
  classical
  let P : ℕ := ∏ p ∈ intervalSievePrimes S z,p
  let T : Finset ℕ := P.divisors.filter (fun d : ℕ => (d:ℝ) ≤ y)
  have hP := intervalSieve_squarefree S z
  have hT (d : ℕ) (hd : d ∈ T) : d ∣ P ∧ 1 ≤ d ∧ (d:ℝ) ≤ y := by
    obtain ⟨hd,hy⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd,hP0⟩ := Nat.mem_divisors.mp hd
    have h0 : d ≠ 0 := by
      intro h
      subst d
      exact hP0 (zero_dvd_iff.mp hd)
    exact ⟨hd,Nat.one_le_iff_ne_zero.mpr h0,hy⟩
  have hcard : (T.card:ℝ) ≤ y := by
    have hsub : T ⊆ Finset.Icc 1 ⌊y⌋₊ := by
      intro d hd
      exact Finset.mem_Icc.mpr ⟨(hT d hd).2.1,Nat.le_floor (hT d hd).2.2⟩
    have hc : (T.card:ℝ) ≤ ⌊y⌋₊ := by
      exact_mod_cast (by simpa using Finset.card_le_card hsub : T.card ≤ ⌊y⌋₊)
    exact hc.trans (Nat.floor_le (by linarith))
  rw [← Finset.sum_filter]
  change (∑ d ∈ T,(3:ℝ)^ArithmeticFunction.cardDistinctFactors d*
    |rem (s := (intervalPrimeSieve S X z y hy).toBoundingSieve) d|) ≤ _
  calc
    _ ≤ ∑ _d ∈ T,2*y^2 := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hd,h1,hdy⟩ := hT d hd
      have hweight : (3:ℝ)^ArithmeticFunction.cardDistinctFactors d ≤ d := by
        exact_mod_cast odd_sieve_divisor_weight (hd.trans (intervalSieve_prod_dvd S z))
      have hr := intervalPrimeSieve_rem_le S X z y hy (hP.squarefree_of_dvd hd)
      have hdR : (1:ℝ) ≤ d := by exact_mod_cast h1
      have hh := mul_le_mul hweight hr (abs_nonneg _) (by positivity : (0:ℝ) ≤ d)
      nlinarith
    _ = (T.card:ℝ)*(2*y^2) := by simp
    _ ≤ y*(2*y^2) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

def intervalSifted (S X z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun n => (∏ p ∈ intervalSievePrimes S z,p).Coprime n)

lemma intervalSifted_selberg (S X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    ((intervalSifted S X z).card:ℝ) ≤
      X/selbergBoundingSum (intervalPrimeSieve S X z y hy)+2*y^3 := by
  have he : siftedSum (s := (intervalPrimeSieve S X z y hy).toBoundingSieve) =
      ((intervalSifted S X z).card:ℝ) := by
    change (∑ n ∈ Finset.Icc 1 X,
      if (∏ p ∈ intervalSievePrimes S z,p).Coprime n then (1:ℝ) else 0) = _
    rw [← Finset.sum_filter]
    simp [intervalSifted]
  rw [← he]
  exact (selberg_bound_simple _).trans
    (add_le_add le_rfl (intervalPrimeSieve_error_sum S X z y hy))

end TotientAsymptotic

end

end OAI
