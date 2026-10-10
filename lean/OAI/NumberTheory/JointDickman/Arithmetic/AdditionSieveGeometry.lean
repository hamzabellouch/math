import OAI.NumberTheory.JointDickman.Amplification.AdditionProgressionGeometry
import OAI.NumberTheory.JointDickman.Arithmetic.LargeDivisorReciprocals

namespace OAI

/-! # Removing the actual coefficient primes in the addition sieve -/

namespace JointDickman
open Finset Classical

noncomputable def additionExcludedPrimes (B e b : ℕ) : Finset ℕ :=
  (e*b).primeFactors ∩ auxiliaryPrimes B

theorem additionExcludedPrimes_subset (B e b : ℕ) :
    additionExcludedPrimes B e b ⊆ auxiliaryPrimes B := inter_subset_right

theorem additionExcludedPrimes_product_le {B e b : ℕ} (he : 0 < e) (hb : 0 < b) :
    (∏ p ∈ additionExcludedPrimes B e b, p : ℕ) ≤ e*b := by
  apply Nat.le_of_dvd (Nat.mul_pos he hb)
  exact (prod_dvd_prod_of_subset _ _ id inter_subset_left).trans (Nat.prod_primeFactors_dvd (e*b))

theorem addition_progression_good_primes {B e j b z₀ : ℕ} {g : ℝ}
    (he : 0 < e) (hb : 0 < b) (hj : 0 < j) (hcut : j ≤ auxiliaryCutoff B)
    {c : ℤ} (hbase : (e : ℤ)*z₀ = b+(j : ℤ)*c) :
    ∀ p ∈ primePrefix B g (auxiliaryPrimes B) \ additionExcludedPrimes B e b,
      (j : ZMod p) ≠ 0 ∧ (e : ZMod p) ≠ 0 ∧
        (z₀ : ZMod p)*e-(c : ZMod p)*j ≠ 0 := by
  intro p hp
  obtain ⟨hpQ,hpE⟩ := mem_sdiff.mp hp
  have hQ : primePrefix B g (auxiliaryPrimes B) ⊆ auxiliaryPrimes B := by
    unfold primePrefix
    split_ifs
    · exact filter_subset _ _
    · exact subset_rfl
  have hpP := hQ hpQ
  have hprime := auxiliaryPrimes_prime B p hpP
  have hbig : auxiliaryCutoff B < p := by exact_mod_cast (mem_filter.mp hpP).2
  have hn : ¬p ∣ e*b := by
    intro hd
    exact hpE (mem_inter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hprime,hd,(Nat.mul_pos he hb).ne'⟩,hpP⟩)
  have hne : ¬p ∣ e := fun hd => hn (dvd_mul_of_dvd_left hd b)
  have hnb : ¬p ∣ b := fun hd => hn (dvd_mul_of_dvd_right hd e)
  have hnj : ¬p ∣ j := Nat.not_dvd_of_pos_of_lt hj (lt_of_le_of_lt hcut hbig)
  have hdet := addition_progression_determinant hbase
  have hcast : (z₀ : ZMod p)*e-(c : ZMod p)*j = (b : ZMod p) := by
    simpa only [Int.cast_sub,Int.cast_mul,Int.cast_natCast] using congrArg (fun z : ℤ => (z : ZMod p)) hdet
  refine ⟨?_,?_,?_⟩
  · simpa only [ne_eq,ZMod.natCast_eq_zero_iff] using hnj
  · simpa only [ne_eq,ZMod.natCast_eq_zero_iff] using hne
  · rw [hcast]
    simpa only [ne_eq,ZMod.natCast_eq_zero_iff] using hnb

end JointDickman

end OAI
