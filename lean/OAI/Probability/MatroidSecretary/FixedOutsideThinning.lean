import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
# Source accounting contracts

The finite-fiber expectation below expresses conditioning on all test coordinates
outside the focal group. In contrast to an expectation over the entire test mask,
it retains the conditional quantifier in `lem:all-orders` (accounting.tex).
-/

namespace MatroidProphet

open Set Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Fix every test bit outside `G`, and average only the fresh bits inside `G`.
The contracted base may depend arbitrarily on the fixed outside mask. -/
theorem fixed_outside_thinning_rank
    (M : Matroid α) (hE : M.E = Set.univ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (G A : Finset α) (hAG : Disjoint A G) (S : Set α) (hS : S ⊆ (G : Set α))
    (P : Finset α → Set α)
    (hP : ∀ B : Finset α, B ⊆ G → P (A ∪ B) = P A) :
    t * (conditionalRank M S (P A) : ℝ) ≤
      bitsExpectation (fun _ => t) G
        (fun B => (conditionalRank M (S ∩ ((A ∪ B : Finset α) : Set α))
          (P (A ∪ B)) : ℝ)) := by
  classical
  have hdis : S ∩ (A : Set α) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro e ⟨heS, heA⟩
    exact Finset.disjoint_left.mp hAG heA (hS heS)
  have hb := independent_thinning_rank M hE G S.toFinset
    (fun e he => hS (by simpa only [Set.mem_toFinset] using he)) (P A) t ht0 ht1
  calc
    _ ≤ bitsExpectation (fun _ => t) G
        (fun B => (conditionalRank M (S ∩ (B : Set α)) (P A) : ℝ)) := by
      simpa only [Finset.coe_inter, Set.coe_toFinset] using hb
    _ = _ := by
      apply bitsExpectation_congr
      intro B hB
      rw [hP B hB]
      rw [Finset.coe_union, Set.inter_union_distrib_left, hdis, Set.empty_union]

/-- The source's test-thinning inequality conditional on the complete outside
configuration, not on an arrival order and not merely after averaging it away. -/
theorem fixed_outside_finalRankStatistic
    (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (h final : ℕ) (O : Set α) (ε : Fin 2) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (A : Finset α) (hA : Disjoint A (G h)) :
    t * (finalRankStatistic M hE κ D C
      (fun j => (A : Set α) ∩ (G j : Set α)) h final (G h) O Set.univ ε : ℝ) ≤
    bitsExpectation (fun _ : α => t) (G h) (fun B =>
      (finalRankStatistic M hE κ D C
        (fun j => ((A ∪ B : Finset α) : Set α) ∩ (G j : Set α)) h final
        (G h) O ((A ∪ B : Finset α) : Set α) ε : ℝ)) := by
  simp only [finalRankStatistic, Set.inter_univ, Nat.cast_sum,
    bitsExpectation_sum, mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  apply fixed_outside_thinning_rank M hE t ht0 ht1 (G h) A hA
  · exact fun e he => nominalLayerSet_subset M hE κ D C h (G h) ε b he.1
  · intro B hB
    rw [lowerCompetition_ignore_focal M hE κ D C G hG b.val.val h A B hB]

end MatroidProphet

end OAI
