import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.GreedyOutputExpected

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [PseudoMetricSpace V] {a : ℕ}
noncomputable def ballSet (F : Finset V) (w : Fin a → V) (radius : Fin a → ℝ)
    (i : Fin a) : Finset V := by
  classical
  exact F.filter (fun x => dist (w i) x ≤ radius i)
abbrev CopiedBall (F : Finset V) (w : Fin a → V) (radius : Fin a → ℝ) :=
  (i : Fin a) × ↥(ballSet F w radius i)
def copiedPart (F : Finset V) (w : Fin a → V) (radius : Fin a → ℝ)
    (e : CopiedBall F w radius) : Fin a := e.1
def copiedLoc (F : Finset V) (w : Fin a → V) (radius : Fin a → ℝ)
    (e : CopiedBall F w radius) : V := e.2.val
lemma copiedLoc_mem (F : Finset V) (w : Fin a → V) (radius : Fin a → ℝ)
    (e : CopiedBall F w radius) : copiedLoc F w radius e ∈ F :=
  (Finset.mem_filter.mp e.2.property).1
lemma copiedLoc_distance (F : Finset V) (w : Fin a → V) (radius : Fin a → ℝ)
    (e : CopiedBall F w radius) :
    dist (w (copiedPart F w radius e)) (copiedLoc F w radius e) ≤
      radius (copiedPart F w radius e) :=
  (Finset.mem_filter.mp e.2.property).2
lemma copiedPart_surjective (F : Finset V) (w : Fin a → V) (radius : Fin a → ℝ)
    (hn : ∀ i, (ballSet F w radius i).Nonempty) :
    Function.Surjective (copiedPart F w radius) := by
  intro i
  obtain ⟨x,hx⟩ := hn i
  exact ⟨⟨i,⟨x,hx⟩⟩,rfl⟩
lemma copiedBall_card_le (F : Finset V) (w : Fin a → V) (radius : Fin a → ℝ) :
    Fintype.card (CopiedBall F w radius) ≤ a * F.card := by
  classical
  rw [Fintype.card_sigma]
  calc
    ∑ i : Fin a, Fintype.card ↥(ballSet F w radius i) ≤ ∑ _ : Fin a, F.card := by
      apply Finset.sum_le_sum
      intro i _
      rw [Fintype.card_coe]
      exact Finset.card_filter_le F (fun x => dist (w i) x ≤ radius i)
    _ = a * F.card := by simp

lemma copied_comparison (F : Finset V) (w center : Fin a → V) (radius : Fin a → ℝ)
    (hF : ∀ i, center i ∈ F) (hball : ∀ i, dist (w i) (center i) ≤ radius i) :
    (∀ i, (ballSet F w radius i).Nonempty) ∧
    ∃ X : Finset (CopiedBall F w radius),
      Categorical.PartitionFeasible (copiedPart F w radius) X ∧ X.card = a ∧
      ∀ i, ∃ e ∈ X, copiedLoc F w radius e = center i := by
  classical
  have hc : ∀ i, center i ∈ ballSet F w radius i := by
    intro i
    exact Finset.mem_filter.mpr ⟨hF i,hball i⟩
  let o : Fin a → CopiedBall F w radius := fun i => ⟨i,⟨center i,hc i⟩⟩
  have ho : ∀ i, copiedPart F w radius (o i) = i := fun _ => rfl
  refine ⟨fun i => ⟨center i,hc i⟩, Finset.univ.image o,
    Categorical.partitionFeasible_image _ o ho,?_,?_⟩
  · have hinj : Function.Injective o := fun i j h => congrArg Sigma.fst h
    rw [Finset.card_image_of_injective _ hinj]
    simp
  · intro i
    exact ⟨o i,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩,rfl⟩
end MetricKMedianRecovery.Completion

end OAI
