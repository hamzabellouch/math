import OAI.NumberTheory.TwoPoint.Bounds.ComplexCanonicalDeletion
import OAI.NumberTheory.TwoPoint.Bounds.ComplexCenteringSum
import OAI.NumberTheory.TwoPoint.Bounds.ComplexPartialProfiles
import OAI.NumberTheory.TwoPoint.Bounds.CenteredBinIdentity

namespace OAI

/-! The uncut complex graph is the literal centered tuple correlation. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma untwistedUncutPrefix_centered {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (Q : Finset ℕ) (eligible : ℕ → ℕ → Prop) (h N : ℕ) (F G : ℕ → ℂ) :
    untwistedUncutPrefix P Q eligible h (fun _ _ _ => True)
      (fun z => F z.toNat) (fun z => G z.toNat) N =
      positivePrefix (fun n => ∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
        tupleComplexCenteredProfile P q eligible F G h n) N / (N : ℂ) := by
  unfold untwistedUncutPrefix
  congr 1
  unfold positivePrefix
  apply sum_congr rfl
  intro n _
  dsimp only
  rw [primeTupleDivisors, sum_image]
  · rw [sum_comm]
    apply sum_congr rfl
    intro q hq
    simp only [tupleComplexCenteredProfile, mul_sum]
    apply sum_congr rfl
    intro x _
    rw [uncutNumericalEdge_untwist Q eligible h (fun _ _ _ => True)
      (fun z => F z.toNat) (fun z => G z.toNat) (∏ j, (x j).val) q
      (n + 1 : ℕ) _ (by omega) (by positivity)]
    simp only [true_and, hq, Int.toNat_natCast, and_true,
      Int.natCast_dvd_natCast, Complex.ofReal_mul]
    have hm : ((n + 1 : ℕ) : ℤ) + (h * q * ∏ j, (x j).val : ℕ) =
        ((n + 1 + h * (q * ∏ j, (x j).val) : ℕ) : ℤ) := by push_cast; ring
    rw [hm]
    simp only [Int.toNat_natCast]
    unfold natDivisibilityIndicator
    split_ifs <;> simp_all
    ring
  · intro x _ y _ hxy
    exact primeTuple_injective hprime hdisjoint hxy

lemma tupleComplexPartialProfile_empty {J : ℕ} (P : Fin J → Finset ℕ)
    (q : ℕ) (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h n : ℕ) :
    tupleComplexPartialProfile P ∅ q eligible F G h n =
      ∑ x : (j : Fin J) → P j,
        if eligible (∏ j, (x j).val) q then
          natDivisibilityIndicator (q * ∏ j, (x j).val) n *
            (F n * G (n + h * (q * ∏ j, (x j).val)))
        else 0 := by
  unfold tupleComplexPartialProfile
  apply sum_congr rfl
  intro x _
  have he : (∏ j : {j // j ∉ (∅ : Finset (Fin J))}, (x j).val) =
      ∏ j, (x j).val := (prod_subtype univ (by simp) (fun j => (x j).val)).symm
  simp only [Fintype.prod_empty, Nat.cast_one, inv_one, one_mul, he]

noncomputable def fullComplexBin {J : ℕ} (P : Fin J → Finset ℕ)
    (Q : Finset ℕ) (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h : ℕ) (T : ℝ) : ℂ :=
  ∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
    (positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) ⌊T⌋₊ / (T : ℂ))

noncomputable def nonrawComplexBin {J : ℕ} (P : Fin J → Finset ℕ)
    (Q : Finset ℕ) (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h : ℕ) (T : ℝ) : ℂ :=
  ∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
    ((positivePrefix (tupleComplexCenteredProfile P q eligible F G h) ⌊T⌋₊ -
      positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) ⌊T⌋₊) / (T : ℂ))

lemma weighted_complex_uncut_sub_full {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (Q : Finset ℕ) (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h : ℕ) (T : ℝ) :
    ((⌊T⌋₊ : ℂ) / (T : ℂ)) * untwistedUncutPrefix P Q eligible h (fun _ _ _ => True)
      (fun z => F z.toNat) (fun z => G z.toNat) ⌊T⌋₊ -
        fullComplexBin P Q eligible F G h T = nonrawComplexBin P Q eligible F G h T := by
  rw [untwistedUncutPrefix_centered P hprime hdisjoint,
    prefix_scalar_real_denominator, positivePrefix_sum_finite, sum_div]
  simp only [positivePrefix_const_mul, fullComplexBin, nonrawComplexBin, mul_div_assoc]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro q _
  ring

end TwoPointCorrelations

end OAI
