import OAI.NumberTheory.Jacobsthal.Estimates.FactorDividesAbscissa

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem common_prime_product_dvd (P : Finset ℕ) (a : ℕ → ℤ) {q r : ℚ}
    (hqr : q ≠ r) (hP : ∀ p ∈ P,p.Prime) :
    (∏ p ∈ commonAligners P a q r,p) ∣ (determinant q r).natAbs := by
  have hn := Int.natAbs_ne_zero.mpr (determinant_ne_zero hqr)
  have hsub : commonAligners P a q r ⊆ (determinant q r).natAbs.primeFactors := by
    intro p hp
    obtain ⟨hpP,hq,hr⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hP p hpP,Int.natCast_dvd.mp (common_alignment_dvd a q r p hq hr),hn⟩
  exact (Finset.prod_dvd_prod_of_subset _ _ id hsub).trans (Nat.prod_primeFactors_dvd _)

theorem common_primes_power_height_bound (P : Finset ℕ) (a : ℕ → ℤ) {q r : ℚ}
    (hqr : q ≠ r) (hP : ∀ p ∈ P,p.Prime) {z α C : ℝ}
    (hz : 1 < z) (hα : 0 < α) (hlarge : ∀ p ∈ P,z^α ≤ (p : ℝ))
    (hheight : ((determinant q r).natAbs : ℝ) ≤ z^C) :
    ((commonAligners P a q r).card : ℝ) ≤ C/α := by
  have hprod : (∏ p ∈ commonAligners P a q r,p) ≤ (determinant q r).natAbs :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr (determinant_ne_zero hqr)))
      (common_prime_product_dvd P a hqr hP)
  have hpow : z^(α*((commonAligners P a q r).card : ℝ)) ≤ z^C := by
    calc
      _ = ∏ _p ∈ commonAligners P a q r,z^α := by
        rw [Finset.prod_const,Real.rpow_mul_natCast (by linarith : 0 ≤ z)]
      _ ≤ ∏ p ∈ commonAligners P a q r,(p : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg (by linarith) _)
          (fun p hp => hlarge p (Finset.mem_filter.mp hp).1)
      _ = ((∏ p ∈ commonAligners P a q r,p : ℕ) : ℝ) := by simp
      _ ≤ ((determinant q r).natAbs : ℝ) := by exact_mod_cast hprod
      _ ≤ _ := hheight
  have h := (Real.rpow_le_rpow_left_iff hz).mp hpow
  apply (le_div_iff₀ hα).mpr
  nlinarith only [h]

end ErdosInverseAlignment

end

section

namespace ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem prime_rational_list_bound (P : Finset ℕ) (a : ℕ → ℤ) (HA HD : ℕ)
    {z α C c : ℝ} (hz : 1 < z) (hα : 0 < α) (hC : 0 ≤ C) (hc : 0 < c)
    (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,z^α ≤ (p : ℝ))
    (hheight : ((2*HA*HD : ℕ) : ℝ) ≤ z^C) (hPpos : 0 < P.card)
    (henough : 2*(C/α) ≤ c^2*(P.card : ℝ)) :
    ((rationalList P a HA HD c).card : ℝ) ≤ 2/c^2 := by
  apply ErdosInverseIncidence.dense_incidence_card_bound
    (rationalList P a HA HD c) P (fun q p => aligns a q p) hc (div_nonneg hC hα.le) hPpos
  · intro q hq
    exact (mem_rationalList P a HA HD c q).mp hq |>.2.2
  · intro q hq r hr hqr
    obtain ⟨hqa,hqd,_⟩ := (mem_rationalList P a HA HD c q).mp hq
    obtain ⟨hra,hrd,_⟩ := (mem_rationalList P a HA HD c r).mp hr
    apply common_primes_power_height_bound P a hqr hP hz hα hlarge
    exact (show ((determinant q r).natAbs : ℝ) ≤ ((2*HA*HD : ℕ) : ℝ) by
      exact_mod_cast determinant_height q r HA HD hqa hra hqd hrd).trans hheight
  · exact henough

theorem prime_rational_list_card_le_ceil (P : Finset ℕ) (a : ℕ → ℤ) (HA HD : ℕ)
    {z α C c : ℝ} (hz : 1 < z) (hα : 0 < α) (hC : 0 ≤ C) (hc : 0 < c)
    (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,z^α ≤ (p : ℝ))
    (hheight : ((2*HA*HD : ℕ) : ℝ) ≤ z^C) (hPpos : 0 < P.card)
    (henough : 2*(C/α) ≤ c^2*(P.card : ℝ)) :
    (rationalList P a HA HD c).card ≤ ⌈2/c^2⌉₊ := by
  have h := (prime_rational_list_bound P a HA HD hz hα hC hc hP hlarge hheight hPpos henough).trans
    (Nat.le_ceil (2/c^2))
  exact_mod_cast h

end ErdosInverseAlignment

end

end Erdos970

end OAI
