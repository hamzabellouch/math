import Mathlib
import OAI.Probability.BinarySweep.FiniteLaws.SumDite
import OAI.Probability.BinarySweep.Trajectories.IsolatedCancellation

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

def restrictPlacement {t : Fin (b+1)} (x : Placement H k t) (A : Finset (Fin k)) :
    Placement H (Fintype.card A) t where
  toFun i := x ((Fintype.equivFin A).symm i).val
  inj' _ _ he := (Fintype.equivFin A).symm.injective
    (Subtype.ext (x.injective he))

lemma restrictPlacement_event (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (A : Finset (Fin k)) (g : ConditionalChoices H) :
    placementBijection H (Fintype.card A) g (restrictPlacement H x A)=restrictPlacement H y A ↔
      ∀i ∈ A, gridSweep bits g.val (x i).val=(y i).val := by
  constructor
  · intro he i hi
    have hh := congrArg (fun q => (q (Fintype.equivFin A ⟨i,hi⟩)).val) he
    change gridSweep bits g.val (x ((Fintype.equivFin A).symm
      (Fintype.equivFin A ⟨i,hi⟩)).val).val =
      (y ((Fintype.equivFin A).symm (Fintype.equivFin A ⟨i,hi⟩)).val).val at hh
    simpa only [Equiv.symm_apply_apply] using hh
  · intro he
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact he _ ((Fintype.equivFin A).symm i).property

lemma endpointProbability_conditional {I : Type*} [Fintype I] [DecidableEq I]
    (z : ℝ) (A : Finset I) (e : I → GridSlot bits × GridSlot bits) :
    endpointProbability H z A e =
      conditionalEventWeight H z (fun g => ∀i ∈ A, gridSweep bits g (e i).1=(e i).2) := by
  unfold endpointProbability endpointMass conditionalEventWeight conditionalChoiceWeight
  have hh (g : ConditionalChoices H) :
      (if ∀i ∈ A, gridSweep bits g.val (e i).1=(e i).2 then
        gridWeight bits z g.val / conditionalNormalizer H z else 0) =
      (if ∀i ∈ A, gridSweep bits g.val (e i).1=(e i).2 then gridWeight bits z g.val else 0) /
        conditionalNormalizer H z := by split_ifs <;> simp
  have hR : (∑g : ConditionalChoices H,
      if ∀i ∈ A, gridSweep bits g.val (e i).1=(e i).2 then
        gridWeight bits z g.val / conditionalNormalizer H z else 0) =
      (∑g : ConditionalChoices H, if ∀i ∈ A, gridSweep bits g.val (e i).1=(e i).2 then
        gridWeight bits z g.val else 0) / conditionalNormalizer H z := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g _
    exact hh g
  refine Eq.trans ?_ (Eq.trans hR.symm ?_)
  · congr 1
    have hs := sum_dite_zero (pathEvent H) (fun g _ =>
      if ∀i ∈ A, gridSweep bits g (e i).1=(e i).2 then gridWeight bits z g else 0)
    refine Eq.trans ?_ (hs.trans ?_)
    · apply Finset.sum_congr rfl
      intro g _
      split_ifs <;> simp_all
    · apply Finset.sum_congr (by ext sample; simp)
      intro g _
      rfl
  · apply Finset.sum_congr rfl
    intro g _
    split_ifs <;> rfl

theorem endpointProbability_placement (z : ℝ)
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) (A : Finset (Fin k)) :
    endpointProbability H z A (fun i => ((x i).val,(y i).val)) =
      placementProbability H z (restrictPlacement H x A) (restrictPlacement H y A) := by
  rw [endpointProbability_conditional]
  unfold conditionalEventWeight placementProbability
  apply Finset.sum_congr rfl
  intro g _
  simp only [restrictPlacement_event]
  split_ifs <;> rfl

end BinaryCoordinateSweeps

end

end OAI
