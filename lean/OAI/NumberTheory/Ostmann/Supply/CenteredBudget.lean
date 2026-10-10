import OAI.NumberTheory.Ostmann.Preliminaries.SiftedEnergy
import OAI.NumberTheory.Ostmann.Supply.CenteredPrimitiveEnergy
import OAI.NumberTheory.Ostmann.Supply.CompletionInterchange

namespace OAI

noncomputable section
namespace Ostmann.Supply
open Finset
open CompletionCounting
open scoped BigOperators

def boundedSupportWeight (S : ∀ p : ℕ, Finset (ZMod p)) (R p : ℕ) : ℝ :=
  if p.Prime ∧ p ≤ R then supportRatio S p else 1

theorem boundedSupportWeight_pos (S : ∀ p : ℕ, Finset (ZMod p)) (R : ℕ)
    (hS : ∀ p, p.Prime → p ≤ R → 0 < supportRatio S p) (p : ℕ) :
    0 < boundedSupportWeight S R p := by
  unfold boundedSupportWeight
  split_ifs with h
  · exact hS p h.1 h.2
  · norm_num

theorem primeProduct_boundedSupportWeight (S : ∀ p : ℕ, Finset (ZMod p))
    {R n : ℕ} (hn : n ≤ R) :
    primeProduct (boundedSupportWeight S R) n = primeProduct (supportRatio S) n := by
  apply prod_congr rfl
  intro p hp
  exact ite_eq_left ⟨Nat.prime_of_mem_primeFactors hp, (Nat.le_of_mem_primeFactors hp).trans hn⟩

theorem primitiveEnergy_centered_expansion_bounded (A : Finset ℕ)
    (S : ∀ p : ℕ, Finset (ZMod p)) {R q : ℕ} (hq : Squarefree q) (hqr : q ≤ R)
    (hS : ∀ a ∈ A, ∀ p, p.Prime → p ≤ R → (a : ZMod p) ∈ S p) :
    primitiveEnergy A q = ∑ t ∈ q.divisors,
      (t : ℝ) * centeredEnergy A S t * primeProduct (boundedSupportWeight S R) (q/t) := by
  rw [primitiveEnergy_centered_expansion A S hq
    (fun a ha p hp => hS a ha p (Nat.prime_of_mem_primeFactors hp)
      ((Nat.le_of_mem_primeFactors hp).trans hqr))]
  apply sum_congr rfl
  intro t ht
  rw [primeProduct_boundedSupportWeight S ((Nat.div_le_self q t).trans hqr)]

theorem sum_primitiveEnergy_squarefree_le (A : Finset ℕ) (R : ℕ) (hR : 0 < R)
    (hA : ∀ a ∈ A, a ≤ R^2) :
    ∑ q ∈ squarefreeUpTo R, primitiveEnergy A q ≤ 96*(R : ℝ)^2/(A.card : ℝ) := by
  let q : squarefreeUpTo R → ℕ := fun x => x.val
  let : ∀ x : squarefreeUpTo R, NeZero (q x) := fun x =>
    ⟨by have := (mem_Icc.mp (mem_filter.mp x.property).1).1; dsimp [q]; omega⟩
  have hb : ∀ x : squarefreeUpTo R, q x ≤ R :=
    fun x => (mem_Icc.mp (mem_filter.mp x.property).1).2
  have hi : Function.Injective q := fun x y h => Subtype.ext h
  have hs := Ostmann.SiftedWeights.primitive_energy_sum_le q hb hi A hA hR
  calc
    _ = ∑ x : squarefreeUpTo R, primitiveEnergy A (q x) := (sum_coe_sort _ _).symm
    _ ≤ _ := by simpa only [primitiveEnergy_eq] using hs

theorem centered_energy_sum_le (A : Finset ℕ) (hAn : A.Nonempty)
    (S : ∀ p : ℕ, Finset (ZMod p)) (R : ℕ) (hR : 0 < R)
    (hA : ∀ a ∈ A, a ≤ R^2)
    (hS : ∀ a ∈ A, ∀ p, p.Prime → p ≤ R → (a : ZMod p) ∈ S p)
    (hpos : ∀ p, p.Prime → p ≤ R → 0 < supportRatio S p)
    (T : Finset ℕ) (hT : ∀ t ∈ T, Squarefree t ∧ t ≤ R)
    {B : ℝ} (hB : 0 < B)
    (hcop : ∀ t ∈ T, ∑ p ∈ t.primeFactors, (1 : ℝ) / p ≤ 1/16)
    (hmean : ∑ p ∈ primesUpTo R, |Real.log (supportRatio S p)| / p ≤ B/16) :
    ∑ t ∈ T, centeredEnergy A S t ≤
      1536 * (R : ℝ) / (A.card : ℝ) * Real.exp B := by
  have hκ := boundedSupportWeight_pos S R hpos
  have hm : ∑ p ∈ primesUpTo R, |Real.log (boundedSupportWeight S R p)| / p ≤ B/16 := by
    convert hmean using 1
    apply sum_congr rfl
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hpr := (mem_Icc.mp (mem_filter.mp hp).1).2
    simp [boundedSupportWeight, hpp, hpr]
  have hbudget := weighted_centered_budget R T (centeredEnergy A S)
    (boundedSupportWeight S R) (centeredEnergy_nonneg A S) hκ hT hB hcop hm
  have heq : (∑ q ∈ squarefreeUpTo R, ∑ t ∈ q.divisors,
      (t : ℝ) * centeredEnergy A S t * primeProduct (boundedSupportWeight S R) (q/t)) =
      ∑ q ∈ squarefreeUpTo R, primitiveEnergy A q := by
    apply sum_congr rfl
    intro q hq
    exact (primitiveEnergy_centered_expansion_bounded A S (mem_filter.mp hq).2
      (mem_Icc.mp (mem_filter.mp hq).1).2 hS).symm
  rw [heq] at hbudget
  have hlarge := hbudget.trans (sum_primitiveEnergy_squarefree_le A R hR hA)
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast card_ne_zero.mpr hAn
  have hc : 0 < (R : ℝ)/16 * Real.exp (-B) := by positivity
  calc
    _ ≤ (96*(R : ℝ)^2/(A.card : ℝ)) / ((R : ℝ)/16 * Real.exp (-B)) :=
      (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hlarge)
    _ = _ := by
      rw [Real.exp_neg]
      field_simp
      ring

theorem sample_card_le_of_log_budget (A : Finset ℕ) (hAn : A.Nonempty)
    (S : ∀ p : ℕ, Finset (ZMod p)) (R : ℕ) (hR : 0 < R)
    (hA : ∀ a ∈ A, a ≤ R^2)
    (hS : ∀ a ∈ A, ∀ p, p.Prime → p ≤ R → (a : ZMod p) ∈ S p)
    (hpos : ∀ p, p.Prime → p ≤ R → 0 < supportRatio S p)
    {B : ℝ} (hB : 0 < B)
    (hmean : ∑ p ∈ primesUpTo R, |Real.log (supportRatio S p)| / p ≤ B/16) :
    (A.card : ℝ) ≤ 1536 * (R : ℝ) * Real.exp B := by
  have ht : ∀ t ∈ ({1} : Finset ℕ), Squarefree t ∧ t ≤ R := by
    intro t ht
    have ht1 : t = 1 := mem_singleton.mp ht
    subst t
    exact ⟨squarefree_one, hR⟩
  have hcop : ∀ t ∈ ({1} : Finset ℕ), ∑ p ∈ t.primeFactors, (1 : ℝ)/p ≤ 1/16 := by
    intro t ht
    have ht1 : t = 1 := mem_singleton.mp ht
    subst t
    norm_num
  have h := centered_energy_sum_le A hAn S R hR hA hS hpos {1} ht hB hcop hmean
  rw [sum_singleton, centeredEnergy_one A hAn S] at h
  have hc : (0 : ℝ) < A.card := by exact_mod_cast card_pos.mpr hAn
  have h' : 1 ≤ (1536 * (R : ℝ) * Real.exp B) / (A.card : ℝ) := by
    convert h using 1
    ring
  simpa only [one_mul] using (le_div_iff₀ hc).mp h'

end Ostmann.Supply

end

end OAI
