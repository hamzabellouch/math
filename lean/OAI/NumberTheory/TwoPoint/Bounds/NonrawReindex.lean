import OAI.NumberTheory.TwoPoint.Bounds.PrimeSubsetSplitting

namespace OAI

/-! Exact numerical reindexing of all nonraw center-band terms. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma primeSubset_product_one_lt_iff (W : Finset ℕ)
    (hW : ∀ p ∈ W, Nat.Prime p) :
    1 < (∏ p ∈ W, p) ↔ W.Nonempty := by
  constructor
  · intro h
    by_contra he
    have hzero : W = ∅ := not_nonempty_iff_eq_empty.mp he
    simp only [hzero, prod_empty, lt_self_iff_false] at h
  · exact primeSubset_product_one_lt W hW

/-- A term is indexed uniquely by its retained integer and removed
integer. The original divisor is their product, without multiplicity. -/
theorem nonraw_prime_reindex (S T : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (hT : T ⊆ S)
    (H τ : ℝ) (θ : ℂ) (G : ℕ → ℕ → ℂ) :
    (∑ D ∈ S.powerset, ∑ W ∈ (D ∩ T).powerset,
      if W.Nonempty ∧ H < ((∏ p ∈ D, p : ℕ) : ℝ) ∧
          ((∏ p ∈ D, p : ℕ) : ℝ) ≤ τ * H
      then ((-θ) ^ W.card / ((∏ p ∈ W, p : ℕ) : ℂ)) *
        G (∏ p ∈ D \ W, p) (∏ p ∈ D, p)
      else 0) =
      ∑ u ∈ retainedPrimeDivisors S, ∑ w ∈ nonrawRoughSupport T H τ u,
        ((-θ) ^ w.primeFactors.card / (w : ℂ)) * G u (u * w) := by
  let F : Finset ℕ → Finset ℕ → ℂ := fun U W =>
    if 1 < (∏ p ∈ W, p) ∧
        H < (((∏ p ∈ U, p) * (∏ p ∈ W, p) : ℕ) : ℝ) ∧
        (((∏ p ∈ U, p) * (∏ p ∈ W, p) : ℕ) : ℝ) ≤ τ * H
    then ((-θ) ^ W.card / ((∏ p ∈ W, p : ℕ) : ℂ)) *
      G (∏ p ∈ U, p) ((∏ p ∈ U, p) * (∏ p ∈ W, p))
    else 0
  calc
    _ = ∑ D ∈ S.powerset, ∑ W ∈ (D ∩ T).powerset, F (D \ W) W := by
      apply sum_congr rfl
      intro D hD
      apply sum_congr rfl
      intro W hW
      have hWD : W ⊆ D := (mem_powerset.mp hW).trans inter_subset_left
      have hprime : ∀ p ∈ W, Nat.Prime p := fun p hp => hS p (mem_powerset.mp hD (hWD hp))
      dsimp only [F]
      simp only [primeSubset_factorization D W hWD,
        primeSubset_product_one_lt_iff W hprime]
    _ = ∑ U ∈ S.powerset, ∑ W ∈ (T \ U).powerset, F U W :=
      centerBand_reindex_retained S T hT F
    _ = ∑ U ∈ S.powerset, ∑ w ∈ nonrawRoughSupport T H τ (∏ p ∈ U, p),
        ((-θ) ^ w.primeFactors.card / (w : ℂ)) *
          G (∏ p ∈ U, p) ((∏ p ∈ U, p) * w) := by
      apply sum_congr rfl
      intro U hU
      exact nonraw_subset_sum U T (fun p hp => hS p (mem_powerset.mp hU hp))
        (fun p hp => hS p (hT hp)) H τ θ
        (fun w => G (∏ p ∈ U, p) ((∏ p ∈ U, p) * w))
    _ = _ := by
      symm
      rw [retainedPrimeDivisors, sum_image (primeSubset_product_injective S hS)]

noncomputable def centerDifference (S T C : Finset ℕ) (a : ℕ → ℂ)
    (A H τ : ℝ) (θ : ℂ) (x : ℕ) (F : ℕ → ℂ) : ℂ :=
  ∑ D ∈ S.powerset,
    if H < ((∏ p ∈ D, p : ℕ) : ℝ) ∧ ((∏ p ∈ D, p : ℕ) : ℝ) ≤ τ * H
    then a (∏ p ∈ D, p) * (A : ℂ) ^ (D ∩ C).card * F (∏ p ∈ D, p) *
      (natDivisibilityIndicator (∏ p ∈ D \ T, p) x *
          (∏ p ∈ D ∩ T, (natDivisibilityIndicator p x - θ / (p : ℂ))) -
        natDivisibilityIndicator (∏ p ∈ D, p) x)
    else 0

/-- The literal partially centered-minus-raw sum is exactly the
numerical `u*w` expansion, before estimating or using multiplicativity. -/
theorem centerDifference_eq_nonraw_sum (S T C : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (hT : T ⊆ S) (hCT : Disjoint C T)
    (a : ℕ → ℂ) (A H τ : ℝ) (θ : ℂ) (x : ℕ) (F : ℕ → ℂ) :
    centerDifference S T C a A H τ θ x F =
      ∑ u ∈ retainedPrimeDivisors S, (A : ℂ) ^ (u.primeFactors ∩ C).card *
        ∑ w ∈ nonrawRoughSupport T H τ u,
          ((nonrawRoughData T H τ a θ u).coefficient w / (w : ℂ)) *
            F (u * w) * natDivisibilityIndicator u x := by
  let G : ℕ → ℕ → ℂ := fun u d =>
    (A : ℂ) ^ (u.primeFactors ∩ C).card * a d * F d * natDivisibilityIndicator u x
  calc
    _ = ∑ D ∈ S.powerset, ∑ W ∈ (D ∩ T).powerset,
        if W.Nonempty ∧ H < ((∏ p ∈ D, p : ℕ) : ℝ) ∧
            ((∏ p ∈ D, p : ℕ) : ℝ) ≤ τ * H
        then ((-θ) ^ W.card / ((∏ p ∈ W, p : ℕ) : ℂ)) *
          G (∏ p ∈ D \ W, p) (∏ p ∈ D, p)
        else 0 := by
      unfold centerDifference
      apply sum_congr rfl
      intro D hD
      have hprimeD : ∀ p ∈ D, Nat.Prime p := fun p hp => hS p (mem_powerset.mp hD hp)
      by_cases hb : H < ((∏ p ∈ D, p : ℕ) : ℝ) ∧ ((∏ p ∈ D, p : ℕ) : ℝ) ≤ τ * H
      · simp only [hb, ite_true, and_true]
        rw [partialCenterBand_nonraw_expansion D T hprimeD θ x, sum_filter, mul_sum]
        apply sum_congr rfl
        intro W hW
        have hWT : W ⊆ T := (mem_powerset.mp hW).trans inter_subset_right
        have hcore : ((∏ p ∈ D \ W, p : ℕ).primeFactors ∩ C).card = (D ∩ C).card := by
          rw [Nat.primeFactors_prod (fun p hp => hprimeD p (mem_sdiff.mp hp).1),
            primeSubset_core_retained C D W (hCT.mono_right hWT)]
        by_cases hne : W.Nonempty
        · simp only [hne, ite_true, G, hcore]
          ring
        · simp only [hne, ite_false, mul_zero]
      · simp only [hb, ite_false, and_false, sum_const_zero]
    _ = ∑ u ∈ retainedPrimeDivisors S, ∑ w ∈ nonrawRoughSupport T H τ u,
        ((-θ) ^ w.primeFactors.card / (w : ℂ)) * G u (u * w) :=
      nonraw_prime_reindex S T hS hT H τ θ G
    _ = _ := by
      apply sum_congr rfl
      intro u _
      rw [mul_sum]
      apply sum_congr rfl
      intro w _
      dsimp only [G, nonrawRoughData]
      ring

end TwoPointCorrelations

end OAI
