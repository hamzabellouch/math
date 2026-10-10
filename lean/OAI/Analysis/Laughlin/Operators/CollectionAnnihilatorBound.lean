import OAI.Analysis.Laughlin.Fock.ContractionBound

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def limitPairWindow (Q : ℕ) (x : Space Q) : ℝ :=
  ∑ p ∈ Finset.range 24, occupationNormSq Q (limitPairEnd Q p x)

noncomputable def sourcePairWindow (Q : ℕ) (x : Space Q) : ℝ :=
  ∑ p ∈ Finset.range 24, occupationNormSq Q (sourcePairEnd Q p x)

theorem collection_limit_annihilator_bound {I : Type*} [Fintype I] (Q : ℕ)
    (p : I → ℕ) (j k : I → Fin (Q+1)) (hp : ∀ i, p i ≤ 23) (x : Space Q) :
    (∑ i, occupationNormSq Q (limitFourEnd Q (p i) (j i) (k i) x)) ≤
      (Fintype.card I : ℝ) * limitPairWindow Q x := by
  calc
    _ ≤ ∑ i : I, limitPairWindow Q x := by
      apply Finset.sum_le_sum
      intro i hi
      apply (limitFour_normSq_le_pair Q (p i) (j i) (k i) x).trans
      change occupationNormSq Q (limitPairEnd Q (p i) x) ≤
        ∑ r ∈ Finset.range 24, occupationNormSq Q (limitPairEnd Q r x)
      exact Finset.single_le_sum
        (f := fun r => occupationNormSq Q (limitPairEnd Q r x))
        (fun r hr => occupationNormSq_nonneg Q _) (Finset.mem_range.mpr (by have h := hp i; omega))
    _ = _ := by simp

theorem collection_source_annihilator_bound {I : Type*} [Fintype I] (Q : ℕ)
    (p : I → ℕ) (j k : I → Fin (Q+1)) (hp : ∀ i, p i ≤ 23) (x : Space Q) :
    (∑ i, occupationNormSq Q (sourceFourEnd Q (p i) (j i) (k i) x)) ≤
      (Fintype.card I : ℝ) * sourcePairWindow Q x := by
  calc
    _ ≤ ∑ i : I, sourcePairWindow Q x := by
      apply Finset.sum_le_sum
      intro i hi
      apply (sourceFour_normSq_le_pair Q (p i) (j i) (k i) x).trans
      change occupationNormSq Q (sourcePairEnd Q (p i) x) ≤
        ∑ r ∈ Finset.range 24, occupationNormSq Q (sourcePairEnd Q r x)
      exact Finset.single_le_sum
        (f := fun r => occupationNormSq Q (sourcePairEnd Q r x))
        (fun r hr => occupationNormSq_nonneg Q _) (Finset.mem_range.mpr (by have h := hp i; omega))
    _ = _ := by simp

end Laughlin.Fock

end OAI
