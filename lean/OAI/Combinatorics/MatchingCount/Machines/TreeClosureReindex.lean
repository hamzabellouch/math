import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.DiscreteLadderSteps

namespace OAI

namespace MatchingFPRAS.UnitRefresh
lemma orderedEnum_lt {A : Type} [Fintype A] [LinearOrder A]
    (i j : Fin (Fintype.card A)) : orderedEnum A i < orderedEnum A j ↔ i < j := by
  change ((Finset.univ : Finset A).orderIsoOfFin (Finset.card_univ) i).val <
    ((Finset.univ : Finset A).orderIsoOfFin (Finset.card_univ) j).val ↔ _
  exact ((Finset.univ : Finset A).orderIsoOfFin (Finset.card_univ)).lt_iff_lt
end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.BottleneckAlgorithm
open Finset

variable {V W α : Type} [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
    [LinearOrder α] [OfNat α 1]
omit [Fintype V] [Fintype W] in
lemma seed_reindex (e : V≃W) (he : ∀ a b,e a<e b ↔ a<b) (w : W→W→α) (a b : V) :
    seed (fun i j=>w (e i) (e j)) a b=seed w (e a) (e b) := by
  simp only [seed,edge,e.injective.eq_iff,he]
lemma advance_reindex (e : V≃W) (w : W→W→α) (a b : V) :
    advance (fun i j=>w (e i) (e j)) a b=advance w (e a) (e b) := by
  unfold advance
  simp only [e.injective.eq_iff]
  split_ifs
  · rfl
  · congr 1
    apply le_antisymm
    · apply Finset.sup'_le
      intro c _
      exact Finset.le_sup' (fun k=>min (w (e a) k) (w k (e b))) (Finset.mem_univ (e c))
    · apply Finset.sup'_le
      intro c _
      obtain ⟨d,rfl⟩:=e.surjective c
      exact Finset.le_sup' (fun k=>min (w (e a) (e k)) (w (e k) (e b))) (Finset.mem_univ d)
lemma close_reindex (e : V≃W) (he : ∀ a b,e a<e b ↔ a<b) (w : W→W→α) (k : ℕ) :
    close (fun i j=>w (e i) (e j)) k=fun i j=>close w k (e i) (e j) := by
  induction k with
  | zero=>funext a b; exact seed_reindex e he w a b
  | succ k ih=>
    simp only [close,ih]
    funext a b
    exact advance_reindex e _ a b
end MatchingFPRAS.BottleneckAlgorithm

end OAI
