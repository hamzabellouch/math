import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePairs
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWeight

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open Construction HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

namespace RetainedRow
section
variable (k j : ℕ) (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)

def term (P : ℕ+) (h : CopiedState k j) (y : OutsideState k j)
    (z : ℤ×HistoryReconstruction.Tree j) (phase : ℂ) : ℂ :=
  retainedHistoryWeight k B V extra mask X Δ W j z.1
    (sourceState k j (P:ℤ) h y) z.2 * phase

def guardPhase (P : ℕ+) (h : CopiedState k j) (y : OutsideState k j)
    (z : ℤ×HistoryReconstruction.Tree j) (phase : ℂ) : ℂ :=
  if TransferSupport k B V extra j z.1 (sourceState k j (P:ℤ) h y) z.2 then phase else 0

theorem term_eq (P : ℕ+) (h : CopiedState k j) (y : OutsideState k j)
    (z : ℤ×HistoryReconstruction.Tree j) (phase : ℂ) :
    term k j B V extra mask X Δ W P h y z phase =
      historyRowTerm k j mask X Δ W P h y z (guardPhase k j B V extra P h y z phase) := by
  unfold term retainedHistoryWeight historyRowTerm guardPhase
  split_ifs <;> simp only [zero_mul,mul_zero]

theorem term_source_unit (hj:j<k) (P : ℕ+) (h : CopiedState k j) (y : OutsideState k j)
    (z : ℤ×HistoryReconstruction.Tree j) (phase : ℂ)
    (hf : term k j B V extra mask X Δ W P h y z phase≠0) :
    IsUnit ((∏i,h i:ℤ):ZMod (P:ℕ)) := by
  have hw : retainedHistoryWeight k B V extra mask X Δ W j z.1
      (sourceState k j (P:ℤ) h y) z.2≠0 := (mul_ne_zero_iff.mp hf).1
  exact (retainedHistoryWeight_support hw).current.source_copied_unit hj P h y z.1

variable {α : Type*} [Fintype α] (μ : FinitePrior α) (h : α → CopiedState k j)
    (y : OutsideState k j) (S : List Bool → Finset ℤ) (path : List Bool) (P : ℕ+)
    (phase : α → SupportedHistory S j path → ℂ)

def grouped (u : ZMod (P:ℕ)) : ℂ :=
  countedGroupedRow μ (fun x z => historyRowTag k j P (h x) z.val.1)
    (fun x z => term k j B V extra mask X Δ W P (h x) y z.val (phase x z)) u

theorem grouped_eq (u : ZMod (P:ℕ)) :
    grouped k j B V extra mask X Δ W μ h y S path P phase u =
      historyGroupedRow k j μ h y S path mask X Δ W P
        (fun x z => guardPhase k j B V extra P (h x) y z.val (phase x z)) u := by
  simp only [grouped,historyGroupedRow,term_eq]

theorem offDiagonal_expansion (hj:j<k) (hprod : ∀x,(∏i,h x i)≠0) :
    historyRowOffDiagonal k j μ h y S path mask X Δ W P
        (fun x z => guardPhase k j B V extra P (h x) y z.val (phase x z)) =
      μ.cmean (fun x => μ.cmean (fun x' =>
        ∑z:SupportedHistory S j path,∑z':SupportedHistory S j path,
          let N := z.val.1*(∏i,h x' i)-z'.val.1*(∏i,h x i)
          if (P:ℤ)∣N ∧ N≠0 then
            term k j B V extra mask X Δ W P (h x) y z.val (phase x z)*
              conj (term k j B V extra mask X Δ W P (h x') y z'.val (phase x' z'))
          else 0)) := by
  have hh := historyRowOffDiagonal_expansion k j μ h y S path mask X Δ W P
    (fun x z => guardPhase k j B V extra P (h x) y z.val (phase x z)) hprod
    (by
      intro x z hz
      apply term_source_unit k j B V extra mask X Δ W hj P (h x) y z.val (phase x z)
      simpa only [term_eq] using hz)
  simpa only [← term_eq] using hh

end
end RetainedRow
end Ostmann.Characters.Template

end

end OAI
