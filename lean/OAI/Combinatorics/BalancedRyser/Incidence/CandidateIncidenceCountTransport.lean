import OAI.Combinatorics.BalancedRyser.Candidates.CandidatePrescriptionTransport
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceModel

namespace OAI

namespace Balanced.CandidateIncidence

noncomputable section
open scoped Classical BigOperators
open MeasureTheory TupleAlignment CandidateRetentionTransport

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance incidenceTransportMeasurableSpace : MeasurableSpace F := ⊤

def choiceTest (R : Test F) (M : MergedPairs F) (C : SplitChoice F) : Prop :=
  R C.tuple C.line.1 (tuplePoint M C.tuple)

theorem model_count_eq_prescriptions (R : Test F) (g : Direction F)
    (M : MergedPairs F) :
    (model R g).count M =
      (((successfulPrescriptions M g).filter
        (fun a => R a.tuple g (tuplePoint M a.tuple))).card : ℝ) := by
  simp only [PatternModel.count, PatternModel.indicator, model, event,
    successfulPrescriptions, Finset.filter_filter, Finset.card_eq_sum_ones,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_filter,
    Set.indicator_apply, Set.mem_ofPred_eq, rootSuccessEvent]

theorem model_count_eq_successfulTest (R : Test F) (g : Direction F)
    (M : MergedPairs F) :
    (model R g).count M =
      ((successfulTest M (fun C => C.line.1 = g ∧ choiceTest R M C)).card : ℝ) := by
  rw [successfulTest_at_target_card]
  rw [model_count_eq_prescriptions]
  apply congrArg (fun prescriptions : Finset (RootPrescription g) =>
    (prescriptions.card : ℝ))
  apply Finset.filter_congr
  intro prescription _
  simp only [choiceTest, RootPrescription.choice_tuple,
    RootPrescription.choice_direction]

theorem allModel_count_eq_successfulTest (R : Test F) (M : MergedPairs F) :
    (allModel R).count M = ((successfulTest M (choiceTest R M)).card : ℝ) := by
  rw [successfulTest_card_eq_sum_prescriptions, Nat.cast_sum]
  rw [allModel_count]
  apply Finset.sum_congr rfl
  intro g _
  rw [← model_count]
  rw [model_count_eq_prescriptions]
  apply congrArg (fun prescriptions : Finset (RootPrescription g) =>
    (prescriptions.card : ℝ))
  apply Finset.filter_congr
  intro prescription _
  simp only [choiceTest, RootPrescription.choice_tuple,
    RootPrescription.choice_direction]

theorem lineHit_model_count (g : Direction F) (L : Line F) (M : MergedPairs F) :
    (model (lineHitTest L) g).count M =
      ((successfulTest M (fun C => C.line.1 = g ∧
        ∃ p ∈ designated M C, OnLine p L)).card : ℝ) := by
  rw [model_count_eq_successfulTest]
  congr 2
  ext C
  simp [choiceTest, lineHitTest, designated]

theorem lineHit_successfulTest_moment_le (g : Direction F) (L : Line F) (s : ℕ) :
    (∫ M, (((successfulTest M (fun C => C.line.1 = g ∧
      ∃ p ∈ designated M C, OnLine p L)).card : ℝ)^s)
      ∂(offsetLaw F).toMeasure) ≤
      (32768 * (((s-1)*4 : ℕ) + 1)^4 : ℝ)^s := by
  have h := lineHit_model_moment_le g L ∅ (fun _ _ => 0) 0 s (by simp)
  have hempty (M : MergedPairs F) :
      (model (lineHitTest L) g).fixCoordinates ∅ (fun _ _ => 0) M = M := by
    funext d
    simp only [PatternModel.fixCoordinates, Finset.notMem_empty, ite_false]
  simp only [PatternModel.fixedExpectation, Nat.zero_add] at h
  simp_rw [hempty] at h
  rw [model_measure] at h
  simpa only [lineHit_model_count] using h

end
end Balanced.CandidateIncidence

end OAI
