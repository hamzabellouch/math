import OAI.NumberTheory.JointDickman.Amplification.GraphEdgePeriod

namespace OAI

/-! # The normalized edge majorant is uniform in the coefficients -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graph_good_lag_ne_zero {B a b c : ℕ} {j : ℤ}
    (hj : j ≠ 0) (hsmall : j.natAbs ≤ auxiliaryCutoff B) :
    ∀ p ∈ graphGoodPrimes B a b c, (j : ZMod p) ≠ 0 := by
  intro p hp hz
  have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd j p).mp hz
  have hnat : p ∣ j.natAbs := Int.natCast_dvd.mp hdiv
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hj) hnat
  have hpgt : auxiliaryCutoff B < p := by
    exact_mod_cast (mem_filter.mp (mem_filter.mp hp).1).2
  omega

theorem graph_bad_primes_product_le {B a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∏ p ∈ auxiliaryPrimes B\graphGoodPrimes B a b c, p) ≤ a*b*c := by
  have hprime : ∀ p ∈ auxiliaryPrimes B\graphGoodPrimes B a b c, p.Prime :=
    fun p hp => auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1
  apply Nat.le_of_dvd (Nat.mul_pos (Nat.mul_pos ha hb) hc)
  apply (primeProduct_dvd_iff _ hprime _).mpr
  intro p hp
  have hnot := (mem_sdiff.mp hp).2
  by_cases hpa : p ∣ a
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpa b) c
  by_cases hpb : p ∣ b
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpb a) c
  by_cases hpc : p ∣ c
  · exact dvd_mul_of_dvd_right hpc (a*b)
  exact False.elim (hnot (mem_filter.mpr ⟨(mem_sdiff.mp hp).1,hpa,hpb,hpc⟩))

theorem graphEdgeMean_bound (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      (a : ℝ)*b*c ≤ Real.exp (10*(B : ℝ)) →
        graphEdgeMean B a b c ≤ K/((a : ℝ)*b) := by
  obtain ⟨K,hK,hbound⟩ := graph_three_root_normalization hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with B hB
  intro a b c ha hb hc hsize
  let S := auxiliaryPrimes B\graphGoodPrimes B a b c
  have hS : S ⊆ auxiliaryPrimes B := sdiff_subset
  have hprod : (∏ p ∈ S, p : ℕ) ≤ Real.exp (10*(B : ℝ)) := by
    have h := graph_bad_primes_product_le (B := B) ha hb hc
    have h' : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (a : ℝ)*b*c := by exact_mod_cast h
    exact h'.trans hsize
  have hSG : auxiliaryPrimes B\S = graphGoodPrimes B a b c :=
    Finset.sdiff_sdiff_eq_self (filter_subset _ _)
  have h := hB S hS hprod
  rw [hSG] at h
  unfold graphEdgeMean
  calc
    _ = ((auxiliaryRatio B^(1/2 : ℝ))^3 *
        ∏ p ∈ graphGoodPrimes B a b c, (1-3/(2*(p : ℝ))))/((a : ℝ)*b) := by ring
    _ ≤ K/((a : ℝ)*b) := div_le_div_of_nonneg_right h (by positivity)

end JointDickman

end OAI
