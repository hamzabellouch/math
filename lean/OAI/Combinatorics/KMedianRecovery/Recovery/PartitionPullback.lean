import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.GreedyOutputExpected
import OAI.Combinatorics.KMedianRecovery.Recovery.Score

namespace OAI

namespace MetricKMedianRecovery.Completion
open Categorical
variable {E B I : Type*} [DecidableEq B] [DecidableEq I]
lemma filter_image_part (partE : E→I) (partB : B→I) (f : E→B)
    (hf : ∀ e,partB (f e)=partE e) (X : Finset E) (i : I) :
    (X.image f).filter (fun e=>partB e=i)=(X.filter (fun e=>partE e=i)).image f := by
  ext b
  simp only [Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨e,he,rfl⟩,hi⟩
    exact ⟨e,⟨he,(hf e) ▸ hi⟩,rfl⟩
  · rintro ⟨e,⟨he,hi⟩,rfl⟩
    exact ⟨⟨e,he,rfl⟩,by rw [hf];exact hi⟩
lemma partition_image {a : ℕ} (partE : E→Fin a) (partB : B→Fin a) (f : E→B)
    (hf : ∀ e,partB (f e)=partE e) (X : Finset E) (hX : PartitionFeasible partE X) :
    PartitionFeasible partB (X.image f) := by
  intro i
  rw [filter_image_part partE partB f hf]
  exact Finset.card_image_le.trans (hX i)
lemma capped_image (base : ℝ) (distance : B→ℝ) (f : E→B) (X : Finset E) :
    cappedCost base distance (X.image f)=cappedCost base (distance ∘ f) X := by
  unfold cappedCost
  exact Finset.fold_image_idem
end MetricKMedianRecovery.Completion

end OAI
