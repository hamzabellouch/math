import OAI.NumberTheory.TwoPoint.Walks.RetainedDivisorMass
import OAI.NumberTheory.TwoPoint.Basic

namespace OAI

/-! Exact expansion of the center-band factors. Each nonempty choice of
constant factors leaves an ordinary divisibility condition for the retained
prime product, and carries precisely one reciprocal removed-prime product. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def natDivisibilityIndicator (d n : ℕ) : ℂ := if d ∣ n then 1 else 0

lemma primeProduct_dvd_iff (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (n : ℕ) :
    (∏ p ∈ S, p) ∣ n ↔ ∀ p ∈ S, p ∣ n := by
  constructor
  · intro h p hp
    exact (dvd_prod_of_mem (fun p : ℕ => p) hp).trans h
  · intro h
    by_cases hn : n = 0
    · simp [hn]
    · have hsub : S ⊆ n.primeFactors := fun p hp => (hS p hp).mem_primeFactors (h p hp) hn
      exact (prod_dvd_prod_of_subset S n.primeFactors (fun p : ℕ => p) hsub).trans
        (Nat.prod_primeFactors_dvd n)

lemma natDivisibilityIndicator_product (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (n : ℕ) :
    (∏ p ∈ S, natDivisibilityIndicator p n) =
      natDivisibilityIndicator (∏ p ∈ S, p) n := by
  by_cases hd : (∏ p ∈ S, p) ∣ n
  · have hp := (primeProduct_dvd_iff S hS n).mp hd
    unfold natDivisibilityIndicator
    simp only [hd, ite_true]
    exact prod_eq_one (fun p hpS => ite_eq_left (hp p hpS))
  · have hn : ¬∀ p ∈ S, p ∣ n := fun h => hd ((primeProduct_dvd_iff S hS n).mpr h)
    push Not at hn
    obtain ⟨p, hp, hpn⟩ := hn
    have hz : (∏ p ∈ S, natDivisibilityIndicator p n) = 0 :=
      prod_eq_zero hp (by simp [natDivisibilityIndicator, hpn])
    rw [hz]
    simp only [natDivisibilityIndicator, hd, ite_false]

theorem centerBand_expansion (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (θ : ℂ) (n : ℕ) :
    (∏ p ∈ S, (natDivisibilityIndicator p n - θ / (p : ℂ))) =
      ∑ W ∈ S.powerset, ((-θ) ^ W.card / ((∏ p ∈ W, p : ℕ) : ℂ)) *
        natDivisibilityIndicator (∏ p ∈ S \ W, p) n := by
  rw [prod_sub]
  apply sum_congr rfl
  intro W _
  rw [natDivisibilityIndicator_product (S \ W)
    (fun p hp => hS p (mem_sdiff.mp hp).1) n]
  rw [prod_div_distrib, prod_const, ← Nat.cast_prod, neg_pow]
  ring

/-- A nonempty removed-prime set contributes a nontrivial factor `w>1`. -/
lemma primeSubset_product_one_lt (W : Finset ℕ) (hW : ∀ p ∈ W, Nat.Prime p)
    (hne : W.Nonempty) : 1 < ∏ p ∈ W, p := by
  obtain ⟨p, hp⟩ := hne
  have hpos : 0 < ∏ p ∈ W, p := prod_pos (fun q hq => (hW q hq).pos)
  have hle : p ≤ ∏ q ∈ W, q := Nat.le_of_dvd hpos (dvd_prod_of_mem (fun q : ℕ => q) hp)
  exact (hW p hp).one_lt.trans_le hle

lemma primeSubset_factorization (S W : Finset ℕ) (hW : W ⊆ S) :
    (∏ p ∈ S \ W, p) * (∏ p ∈ W, p) = ∏ p ∈ S, p := by
  rw [← prod_union sdiff_disjoint, sdiff_union_of_subset hW]

end TwoPointCorrelations

end OAI
