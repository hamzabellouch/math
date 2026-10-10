import OAI.Combinatorics.BalancedRyser.Candidates.CandidateGlobalLineModel
import OAI.Combinatorics.BalancedRyser.Candidates.CandidatePrescriptionTransport

namespace OAI

namespace Balanced.CandidateRetentionTransport

noncomputable section
open scoped Classical BigOperators
open TupleAlignment CandidateIncidence CandidateGlobalLine

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def choiceTest (P : SplitChoice F → Prop) : Test F :=
  fun T g p => P ⟨lineThrough g (p 0), T⟩

theorem model_choiceTest_count (P : SplitChoice F → Prop)
    (g : Direction F) (M : MergedPairs F) :
    (model (choiceTest P) g).count M =
      (((successfulPrescriptions M g).filter (fun a => P (a.choice M))).card : ℝ) := by
  unfold PatternModel.count PatternModel.indicator model event
    choiceTest rootSuccessEvent successfulPrescriptions RootPrescription.choice
  rw [Finset.filter_filter, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  simp only [Nat.cast_one, Set.indicator_apply, Set.mem_ofPred_eq]

theorem allModel_choiceTest_count (P : SplitChoice F → Prop)
    (M : MergedPairs F) :
    (allModel (choiceTest P)).count M = ((successfulTest M P).card : ℝ) := by
  rw [successfulTest_card_eq_sum_prescriptions, Nat.cast_sum]
  change (∑ a : Σ g : Direction F, RootPrescription g,
    (event (choiceTest P) a.1 a.2).indicator (fun _ => (1 : ℝ)) M) = _
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun g _ => model_choiceTest_count P g M)

theorem lineModel_count_eq_successfulTest (L : Line F) (M : MergedPairs F) :
    (lineModel L).count M =
      ((successfulTest M (fun C => ∃ p ∈ designated M C, OnLine p L)).card : ℝ) := by
  rw [← allModel_choiceTest_count]
  unfold PatternModel.count
  apply Finset.sum_congr rfl
  intro a _
  simp [PatternModel.indicator, lineModel, allModel, event, lineHitTest,
    choiceTest, designated, Set.indicator_apply]

theorem gatedLineModel_count_eq_successfulTest (L : Line F) (M : MergedPairs F)
    (hL : L ∉ constituentLines M) :
    (gatedLineModel L).count M =
      ((successfulTest M (fun C => ∃ p ∈ designated M C, OnLine p L)).card : ℝ) := by
  rw [PatternModel.gated_count]
  simpa only [Set.mem_ofPred_eq, ite_eq_left hL] using lineModel_count_eq_successfulTest L M

theorem retained_globalLine_card_le (L : Line F) (M : MergedPairs F)
    (hL : L ∉ constituentLines M) :
    (((candidateVertices M).filter (fun v =>
      ∃ p ∈ CandidateIncidence.points M v, OnLine p L)).card : ℝ) ≤
        2 * (gatedLineModel L).count M := by
  rw [gatedLineModel_count_eq_successfulTest L M hL]
  exact_mod_cast lineHitAll_card_le M L

end
end Balanced.CandidateRetentionTransport

end OAI
