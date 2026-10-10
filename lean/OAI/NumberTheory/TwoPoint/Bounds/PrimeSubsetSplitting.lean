import OAI.NumberTheory.TwoPoint.Bounds.CenterBandReindex
import OAI.NumberTheory.TwoPoint.Bounds.NonrawRoughData
import Mathlib.Data.Nat.GCD.BigOperators

namespace OAI

/-! The subset reindexing gives exactly the numerical rough support:
disjoint prime subsets are equivalent to coprime squarefree products. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma primeSubset_products_coprime (U W : Finset ℕ)
    (hU : ∀ p ∈ U, Nat.Prime p) (hW : ∀ p ∈ W, Nat.Prime p) :
    Nat.Coprime (∏ p ∈ U, p) (∏ p ∈ W, p) ↔ Disjoint U W := by
  rw [Nat.coprime_prod_left_iff]
  constructor
  · intro h
    apply disjoint_left.mpr
    intro p hpU hpW
    have hpp := Nat.coprime_prod_right_iff.mp (h p hpU) p hpW
    exact (Nat.coprime_primes (hU p hpU) (hW p hpW)).mp hpp rfl
  · intro hd p hp
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    apply (Nat.coprime_primes (hU p hp) (hW q hq)).mpr
    intro heq
    subst q
    exact disjoint_left.mp hd hp hq

lemma retainedPrimeDivisors_avoiding (U T : Finset ℕ)
    (hU : ∀ p ∈ U, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p) :
    (retainedPrimeDivisors T).filter (fun w => Nat.Coprime (∏ p ∈ U, p) w) =
      retainedPrimeDivisors (T \ U) := by
  ext w
  constructor
  · intro hw
    obtain ⟨W, hWT, rfl⟩ := mem_image.mp (mem_filter.mp hw).1
    have hsub : W ⊆ T := mem_powerset.mp hWT
    have hd := (primeSubset_products_coprime U W hU (fun p hp => hT p (hsub hp))).mp
      (mem_filter.mp hw).2
    apply mem_image.mpr
    refine ⟨W, mem_powerset.mpr ?_, rfl⟩
    intro p hp
    exact mem_sdiff.mpr ⟨hsub hp, fun hpU => disjoint_left.mp hd hpU hp⟩
  · intro hw
    obtain ⟨W, hW, rfl⟩ := mem_image.mp hw
    have hsub : W ⊆ T \ U := mem_powerset.mp hW
    have hWT : W ⊆ T := fun p hp => (mem_sdiff.mp (hsub hp)).1
    apply mem_filter.mpr
    refine ⟨mem_image.mpr ⟨W, mem_powerset.mpr hWT, rfl⟩, ?_⟩
    apply (primeSubset_products_coprime U W hU (fun p hp => hT p (hWT hp))).mpr
    apply disjoint_left.mpr
    intro p hpU hpW
    exact (mem_sdiff.mp (hsub hpW)).2 hpU

lemma nonrawRoughSupport_of_primeSubset (U T : Finset ℕ)
    (hU : ∀ p ∈ U, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p)
    (H τ : ℝ) :
    nonrawRoughSupport T H τ (∏ p ∈ U, p) =
      (retainedPrimeDivisors (T \ U)).filter (fun w =>
        1 < w ∧ H < (((∏ p ∈ U, p) * w : ℕ) : ℝ) ∧
          (((∏ p ∈ U, p) * w : ℕ) : ℝ) ≤ τ * H) := by
  rw [← retainedPrimeDivisors_avoiding U T hU hT]
  ext w
  simp only [nonrawRoughSupport, mem_filter]
  tauto

lemma primeSubset_core_retained (C D W : Finset ℕ)
    (hCW : Disjoint C W) : (D \ W) ∩ C = D ∩ C := by
  ext p
  simp only [mem_inter, mem_sdiff]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, fun hpW => disjoint_left.mp hCW h.2 hpW⟩, h.2⟩

/-- The removed-subset sum is exactly the numerical rough-support sum,
including its reciprocal coefficient and the prime-factor exponent. -/
theorem nonraw_subset_sum (U T : Finset ℕ)
    (hU : ∀ p ∈ U, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p)
    (H τ : ℝ) (θ : ℂ) (F : ℕ → ℂ) :
    (∑ W ∈ (T \ U).powerset,
      if 1 < (∏ p ∈ W, p) ∧ H < (((∏ p ∈ U, p) * (∏ p ∈ W, p) : ℕ) : ℝ) ∧
          (((∏ p ∈ U, p) * (∏ p ∈ W, p) : ℕ) : ℝ) ≤ τ * H
      then ((-θ) ^ W.card / ((∏ p ∈ W, p : ℕ) : ℂ)) * F (∏ p ∈ W, p)
      else 0) =
      ∑ w ∈ nonrawRoughSupport T H τ (∏ p ∈ U, p),
        ((-θ) ^ w.primeFactors.card / (w : ℂ)) * F w := by
  symm
  rw [nonrawRoughSupport_of_primeSubset U T hU hT, sum_filter,
    retainedPrimeDivisors, sum_image (primeSubset_product_injective (T \ U)
      (fun p hp => hT p (mem_sdiff.mp hp).1))]
  apply sum_congr rfl
  intro W hW
  rw [Nat.primeFactors_prod (fun p hp => hT p
    (mem_sdiff.mp (mem_powerset.mp hW hp)).1)]

end TwoPointCorrelations

end OAI
