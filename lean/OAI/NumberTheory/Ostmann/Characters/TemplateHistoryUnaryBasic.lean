import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyLabelsBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateCharacterTransport
import OAI.NumberTheory.Ostmann.Characters.TemplateHistory
import OAI.NumberTheory.Ostmann.Characters.TemplatePhaseProduct

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable
open HistoryReconstruction

def unaryPivotColumn (k j : ℕ) (i : (schedule k j).Slot) : ℤ :=
  if hj : j<k then graph k j i (pivotSlot k j hj).val else 0

def unaryChildFrequency {j : ℕ} (t : HistoryReconstruction.Tree (j+1)) (b : Bool) : ℤ :=
  if b then t.1.1 else t.1.2

def unaryChildTree {j : ℕ} (t : HistoryReconstruction.Tree (j+1)) (b : Bool) : HistoryReconstruction.Tree j :=
  if b then t.2.1 else t.2.2

def historyUnary (k : ℕ) (width : Role → ℕ) {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (κ : (schedule k 0).Constituent width → ℂ) :
    (j : ℕ) → ℤ → HistoryReconstruction.Tree j → (schedule k j).Constituent width → ℂ
  | 0,s,_,i => κ i * χ (s:ZMod p)^(-1:ℤ)
  | j+1,s,t,⟨.inl (i,b),a⟩ =>
      historyUnary k width χ κ j (unaryChildFrequency t b) (unaryChildTree t b) ⟨i.val,a⟩ ^ copySign b *
        χ ((signedChildFrequency t.1.1 t.1.2 b:ZMod p)/(s:ZMod p)) ^
          (copySign b * unaryPivotColumn k j i.val)
  | j+1,_,t,⟨.inr i,a⟩ =>
      historyUnary k width χ κ j t.1.1 t.2.1 ⟨i.val,a⟩ /
        historyUnary k width χ κ j t.1.2 t.2.2 ⟨i.val,a⟩

def historyRegularKappa (k : ℕ) (width : Role → ℕ) {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (κ : (schedule k 0).Constituent width → ℂ) :
    (j : ℕ) → (schedule k j).Constituent width → ℂ
  | 0,i => κ i
  | j+1,⟨.inl (i,b),a⟩ =>
      historyRegularKappa k width χ κ j ⟨i.val,a⟩ ^ copySign b *
        χ (copySign b:ZMod p)^(copySign b*(rowSign k j i.val:ℤ))
  | _+1,⟨.inr _,_⟩ => 1

@[reducible] def HistoryFrequencyUnits (p : ℕ) : (j : ℕ) → ℤ → HistoryReconstruction.Tree j → Prop
  | 0,s,_ => (s:ZMod p)≠0
  | j+1,s,t => (s:ZMod p)≠0 ∧ HistoryFrequencyUnits p j t.1.1 t.2.1 ∧
      HistoryFrequencyUnits p j t.1.2 t.2.2

theorem HistoryFrequencyUnits.root {p j : ℕ} {s : ℤ} {t : HistoryReconstruction.Tree j}
    (h : HistoryFrequencyUnits p j s t) : (s:ZMod p)≠0 := by
  cases j with
  | zero => exact h
  | succ j => exact h.1

theorem HistoryFrequencyUnits.child {p j : ℕ} {s : ℤ} {t : HistoryReconstruction.Tree (j+1)}
    (h : HistoryFrequencyUnits p (j+1) s t) (b : Bool) :
    HistoryFrequencyUnits p j (unaryChildFrequency t b) (unaryChildTree t b) := by
  cases b
  · exact h.2.2
  · exact h.2.1

theorem historyFrequencyUnits_of_range {p j : ℕ} {path : List Bool} {s : ℤ} {t : HistoryReconstruction.Tree j}
    (S : List Bool → Finset ℤ) (hS : ∀ q f, f∈S q → (f:ZMod p)≠0)
    (ht : HistoryFrequencyLabels.RangeSupported S j path s t) :
    HistoryFrequencyUnits p j s t := by
  induction j generalizing path s with
  | zero => exact hS path s ht
  | succ j ih => exact ⟨hS path s ht.1,ih ht.2.1,ih ht.2.2⟩

def supportedHistoryUnary (k : ℕ) (width : Role → ℕ) {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (κ : (schedule k 0).Constituent width → ℂ)
    (S : List Bool → Finset ℤ) (j : ℕ) (path : List Bool)
    (h : HistoryFrequencyLabels.SupportedHistory S j path) : (schedule k j).Constituent width → ℂ :=
  historyUnary k width χ κ j h.val.1 h.val.2

end Ostmann.Characters.Template

end

end OAI
