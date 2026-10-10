import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyRealizationMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageData

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairedFrequencyAverage
open Construction Characters FrequencyTreeSum HistoryFrequencyResidues

def LabelsIn (S : List Bool → Finset (ℤ × ℤ)) :
    (p : List Bool) → {l : ℕ} → History l → History l → Prop
  | p, _, .leaf a, .leaf b => (a.frequency,b.frequency) ∈ S p
  | p, _, .node a _ _ _ _ left right, .node b _ _ _ _ left' right' =>
    (a.frequency,b.frequency) ∈ S p ∧ LabelsIn S (false::p) left left' ∧
      LabelsIn S (true::p) right right'

def historyAssignment (S : List Bool → Finset (ℤ × ℤ)) :
    (p : List Bool) → {l : ℕ} → (h h' : History l) → LabelsIn S p h h' → Assignment S l p
  | _p, _, .leaf a, .leaf b, hh => ⟨(a.frequency,b.frequency),hh⟩
  | p, _, .node a _ _ _ _ left right, .node b _ _ _ _ left' right', hh =>
    (⟨(a.frequency,b.frequency),hh.1⟩,
      historyAssignment S (false::p) left left' hh.2.1,
      historyAssignment S (true::p) right right' hh.2.2)

@[simp] theorem historyAssignment_root (S : List Bool → Finset (ℤ × ℤ))
    (p : List Bool) {l : ℕ} (h h' : History l) (hh : LabelsIn S p h h') :
    root S (historyAssignment S p h h' hh) = (h.root.frequency,h'.root.frequency) := by
  cases h <;> cases h' <;> rfl

theorem historyAssignment_modulus (S : List Bool → Finset (ℤ × ℤ))
    (p : List Bool) {l : ℕ} (h h' : History l) (hh : LabelsIn S p h h') :
    assignmentModulus S (historyAssignment S p h h' hh) = pairedFrequencyProduct h h' := by
  induction h generalizing p with
  | leaf a =>
    cases h' with
    | leaf b => simp [historyAssignment,assignmentModulus,pairedFrequencyProduct,
        FrequencyPrecision.product,History.frequencies]
  | node a pivot u hp hm left right ihl ihr =>
    cases h' with
    | node b pivot' u' hp' hm' left' right' =>
      change (a.frequency.natAbs*b.frequency.natAbs)*
        (assignmentModulus S (historyAssignment S (false::p) left left' hh.2.1)*
          assignmentModulus S (historyAssignment S (true::p) right right' hh.2.2)) = _
      rw [ihl, ihr]
      simp only [pairedFrequencyProduct,FrequencyPrecision.product,History.frequencies,
        List.map_append,List.prod_append,List.map_cons,List.prod_cons]
      ring

theorem historyAssignment_labelsDivide (S : List Bool → Finset (ℤ × ℤ))
    (p : List Bool) {l : ℕ} (h h' : History l) (hh : LabelsIn S p h h') :
    LabelsDivide S (pairedFrequencyProduct h h') (historyAssignment S p h h' hh) := by
  rw [← historyAssignment_modulus S p h h' hh]
  exact labelsDivide_assignmentModulus S _

end Ostmann.Arithmetic.HistoryPairedFrequencyAverage

end

end OAI
