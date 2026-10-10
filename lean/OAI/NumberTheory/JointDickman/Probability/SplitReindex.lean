import OAI.NumberTheory.JointDickman.Probability.ConditionalFairSplit
import OAI.NumberTheory.JointDickman.Amplification.ThinningRanges

namespace OAI

/-! # Reindexing a site and its first split by the two disjoint parts -/

namespace JointDickman

open Finset

/-- The site-first and coefficient-first descriptions of one fair split
have identical finite expectations, with no asymptotic error. -/
theorem first_split_reindex (P A : Finset ℕ) (hA : A ⊆ P) (F : Finset ℕ → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
      subsetRetentionMass S A * F (S \ A)) =
      ∑ R ∈ P.powerset, fairSelectedRemainingMass P A R * F R := by
  classical
  calc
    _ = ∑ S ∈ P.powerset.filter (fun S => A ⊆ S),
        bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S * (1 / 2 : ℝ)^S.card * F (S \ A) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro S _
      unfold subsetRetentionMass
      split_ifs <;> ring
    _ = ∑ R ∈ P.powerset.filter (fun R => Disjoint A R), fairSelectedRemainingMass P A R * F R := by
      apply sum_bij (fun S _ => S \ A)
      · intro S hS
        obtain ⟨hSP, _⟩ := mem_filter.mp hS
        exact mem_filter.mpr ⟨mem_powerset.mpr (sdiff_subset.trans (mem_powerset.mp hSP)),
          disjoint_sdiff_self_right⟩
      · intro S hS T hT heq
        have hAS := (mem_filter.mp hS).2
        have hAT := (mem_filter.mp hT).2
        calc
          S = A ∪ (S \ A) := (union_sdiff_of_subset hAS).symm
          _ = A ∪ (T \ A) := congrArg (fun R => A ∪ R) heq
          _ = T := union_sdiff_of_subset hAT
      · intro R hR
        obtain ⟨hRP, hd⟩ := mem_filter.mp hR
        refine ⟨A ∪ R, mem_filter.mpr ⟨mem_powerset.mpr
          (union_subset hA (mem_powerset.mp hRP)), subset_union_left⟩, ?_⟩
        ext p
        have hn : p ∈ R → p ∉ A := fun hr ha => disjoint_left.mp hd ha hr
        simp only [mem_sdiff, mem_union]
        tauto
      · intro S hS
        have hAS := (mem_filter.mp hS).2
        have hd : Disjoint A (S \ A) := disjoint_sdiff_self_right
        rw [fairSelectedRemainingMass, ite_eq_left hd, union_sdiff_of_subset hAS]
    _ = _ := by
      rw [sum_filter]
      apply sum_congr rfl
      intro R _
      by_cases hd : Disjoint A R
      · simp only [hd, ite_true]
      · simp only [hd, ite_false, fairSelectedRemainingMass, zero_mul]

/-- Given the first parts, the second fair split is exactly the independent
retention of coefficient primes and addition of remaining primes. -/
theorem second_split_reindex (A R : Finset ℕ) (hd : Disjoint A R)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ C ∈ (A ∪ R).powerset, subsetRetentionMass (A ∪ R) C * F C ((A ∪ R) \ C)) =
      ∑ I ∈ A.powerset, ∑ U ∈ R.powerset,
        subsetRetentionMass A I * subsetRetentionMass R U *
          F (I ∪ U) ((A \ I) ∪ (R \ U)) := by
  rw [sum_powerset_partition A R hd]
  apply sum_congr rfl
  intro I hI
  apply sum_congr rfl
  intro U hU
  have hIA := mem_powerset.mp hI
  have hUR := mem_powerset.mp hU
  rw [subsetRetentionMass_union hd (Subset.refl A) (Subset.refl R) hIA hUR]
  have hdiff : (A ∪ R) \ (I ∪ U) = (A \ I) ∪ (R \ U) := by
    ext p
    have hi := @hIA p
    have hu := @hUR p
    have hn : ¬(p ∈ A ∧ p ∈ R) := fun h => disjoint_left.mp hd h.1 h.2
    simp only [mem_sdiff, mem_union]
    tauto
  rw [hdiff]

end JointDickman

end OAI
