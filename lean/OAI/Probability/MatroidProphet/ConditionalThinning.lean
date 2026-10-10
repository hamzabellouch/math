import OAI.Probability.MatroidProphet.ProductSplit
import OAI.Probability.MatroidProphet.Thinning

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem conditionally_independent_thinning_rank
    (M : Matroid α) (hE : M.E = Set.univ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (V G : Finset α) (hG : G ⊆ V) (S : Set α) (hS : S ⊆ (G : Set α))
    (P : Finset α → Set α)
    (hP : ∀ A B : Finset α, B ⊆ G → P (A ∪ B) = P A) :
    t * bitsExpectation (fun _ => t) V (fun T => (conditionalRank M S (P T) : ℝ)) ≤
      bitsExpectation (fun _ => t) V
        (fun T => (conditionalRank M (S ∩ (T : Set α)) (P T) : ℝ)) := by
  classical
  have heq : bitsExpectation (fun _ => t) V (fun T => (conditionalRank M S (P T) : ℝ)) =
      bitsExpectation (fun _ => t) (V \ G) (fun A => (conditionalRank M S (P A) : ℝ)) := by
    rw [bitsExpectation_split (fun _ => t) V G hG]
    apply bitsExpectation_congr
    intro A hA
    calc
      _ = bitsExpectation (fun _ => t) G (fun _ => (conditionalRank M S (P A) : ℝ)) := by
        apply bitsExpectation_congr
        intro B hB
        rw [hP A B hB]
      _ = _ := bitsExpectation_const _ _ _
  rw [heq, ← bitsExpectation_mul_left, bitsExpectation_split (fun _ => t) V G hG]
  apply bitsExpectation_mono _ (fun _ => ht0) (fun _ => ht1)
  intro A hA
  have hdis : S ∩ (A : Set α) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro e ⟨heS, heA⟩
    exact (Finset.mem_sdiff.mp (hA heA)).2 (hS heS)
  have hb := independent_thinning_rank M hE G S.toFinset
    (fun e he => hS (by simpa only [Set.mem_toFinset] using he)) (P A) t ht0 ht1
  calc
    _ ≤ bitsExpectation (fun _ => t) G
        (fun B => (conditionalRank M (S ∩ (B : Set α)) (P A) : ℝ)) := by simpa only [Finset.coe_inter, Set.coe_toFinset] using hb
    _ = _ := by
      apply bitsExpectation_congr
      intro B hB
      rw [hP A B hB]
      have hset : S ∩ ((A ∪ B : Finset α) : Set α) = S ∩ (B : Set α) := by
        rw [Finset.coe_union, Set.inter_union_distrib_left, hdis, Set.empty_union]
      rw [hset]

end MatroidProphet

end OAI
