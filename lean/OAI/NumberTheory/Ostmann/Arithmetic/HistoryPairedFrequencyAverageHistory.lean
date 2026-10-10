import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageHistoryBudget
import OAI.NumberTheory.Ostmann.Arithmetic.PairedFrequencyActualBudgetBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairedFrequencyAverage
open Construction Conclusion Characters FrequencyTreeSum HistoryFrequencyResidues
open PairedFrequencyActualBudget

theorem rootFrequency_mem_pairedRanges (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (N : ℕ) (p : List Bool) {j : ℕ} (h h' : History j) {outside : List ℕ}
    (hs : h.Supported (frequencyBound Bs BD Bz k L) outside)
    (hs' : h'.Supported (frequencyBound Bs BD Bz k L) outside)
    (hdepth : j+p.length=N) :
    (h.root.frequency,h'.root.frequency) ∈ pairedRanges Bs BD Bz k L N p := by
  have he : N-p.length=j := by omega
  apply (mem_pairedRanges Bs BD Bz k L N p _).mpr
  simpa only [addressBound,he] using
    And.intro ⟨History.supported_root_frequency_ne_zero hs,History.supported_root_frequency_bound hs⟩
      ⟨History.supported_root_frequency_ne_zero hs',History.supported_root_frequency_bound hs'⟩

theorem labelsIn_pairedRanges (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (N : ℕ) (p : List Bool) {j : ℕ} (h h' : History j) {outside : List ℕ}
    (hs : h.Supported (frequencyBound Bs BD Bz k L) outside)
    (hs' : h'.Supported (frequencyBound Bs BD Bz k L) outside)
    (hdepth : j+p.length=N) : LabelsIn (pairedRanges Bs BD Bz k L N) p h h' := by
  induction h generalizing p with
  | leaf a =>
    cases h' with
    | leaf b => exact rootFrequency_mem_pairedRanges Bs BD Bz k L N p _ _ hs hs' hdepth
  | @node j a pivot u hp hm left right ihl ihr =>
    cases h' with
    | node b pivot' u' hp' hm' left' right' =>
      refine ⟨rootFrequency_mem_pairedRanges Bs BD Bz k L N p _ _ hs hs' hdepth, ?_, ?_⟩
      · exact ihl (false::p) left' (History.supported_left hs) (History.supported_left hs')
          (by simp only [List.length_cons]; omega)
      · exact ihr (true::p) right' (History.supported_right hs) (History.supported_right hs')
          (by simp only [List.length_cons]; omega)

def supportedHistoryAssignment (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    {l : ℕ} (h h' : History l) {outside : List ℕ}
    (hs : h.Supported (frequencyBound Bs BD Bz k L) outside)
    (hs' : h'.Supported (frequencyBound Bs BD Bz k L) outside) :
    Assignment (pairedRanges Bs BD Bz k L l) l [] :=
  historyAssignment _ [] h h' (labelsIn_pairedRanges Bs BD Bz k L l [] h h' hs hs' (by simp))

theorem supportedHistoryAssignment_modulus (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    {l : ℕ} (h h' : History l) {outside : List ℕ}
    (hs : h.Supported (frequencyBound Bs BD Bz k L) outside)
    (hs' : h'.Supported (frequencyBound Bs BD Bz k L) outside) :
    assignmentModulus (pairedRanges Bs BD Bz k L l)
      (supportedHistoryAssignment Bs BD Bz k L h h' hs hs') = pairedFrequencyProduct h h' :=
  historyAssignment_modulus _ [] h h' _

theorem supported_history_budget_eq_weight (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (K : ℕ) (C : NNReal) (ε : ℝ) {l : ℕ} (h h' : History l) {outside : List ℕ}
    (hs : h.Supported (frequencyBound Bs BD Bz k L) outside)
    (hs' : h'.Supported (frequencyBound Bs BD Bz k L) outside) :
    ((FrequencyExposure.budget C ε
      (fun p => Characters.Template.ambientData K (pairedFrequencyProduct h h')
        (frequencySchedule h h' p)) l []).value : ℝ) =
      weight (pairedRanges Bs BD Bz k L l) (PairedFrequencyTreeSum.factor (C : ℝ) ε)
        (supportedHistoryAssignment Bs BD Bz k L h h' hs hs') :=
  ambient_schedule_budget_eq_historyWeight _ K _ C ε (frequencySchedule h h')
    (fixedFactorSchedule h h') [] h h' _ (canonical_scheduleMatches h h')

end Ostmann.Arithmetic.HistoryPairedFrequencyAverage

end

end OAI
