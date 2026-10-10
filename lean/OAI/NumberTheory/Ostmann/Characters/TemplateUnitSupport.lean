import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyLabelsBudget
import OAI.NumberTheory.Ostmann.Characters.TemplateIntegerSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open FrequencyExposure HistoryFrequencyLabels

@[reducible] def UnitSupported (k:ℕ) :
    (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→Prop
  | 0,_,_,_ => True
  | j+1,s,x,t => IntegerNodeSupport k j s t.1.1 t.1.2 x ∧
      UnitSupported k j t.1.1
        (childState k j true x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.1 ∧
      UnitSupported k j t.1.2
        (childState k j false x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.2

theorem integerSupport_iff_unitSupported (k R:ℕ) (d:List Bool→Data R)
    (j:ℕ) (p:List Bool) (s:ℤ) (t:HistoryReconstruction.Tree j)
    (hd:DataMatches d j p s t) (x:State k j) :
    IntegerSupport k R d j p x x ↔ UnitSupported k j s x t := by
  induction j generalizing p s with
  | zero => rfl
  | succ j ih =>
    rcases hd.1 with ⟨hs,hs',hv,hw,hv',hw'⟩
    simp only [IntegerSupport,UnitSupported,hs,hs',hv,hw,hv',hw',
      ih _ _ _ hd.2.1,ih _ _ _ hd.2.2]
    exact ⟨fun h=>⟨h.1,h.2.2⟩,fun h=>⟨h.1,h.1,h.2⟩⟩

theorem diagonal_integerSupport_iff (k j:ℕ) (p:List Bool) (s:ℤ)
    (t:HistoryReconstruction.Tree j) (x:State k j) :
    IntegerSupport k (modulus j p s t) (diagonalData j p s t) j p x x ↔
      UnitSupported k j s x t :=
  integerSupport_iff_unitSupported k _ _ j p s t (diagonalData_matches j p s t) x

end Ostmann.Characters.Template

end

end OAI
