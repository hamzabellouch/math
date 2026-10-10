import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryRootSum

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem sum_roots_history_indicators (j:ℕ) (S:List Bool→Finset ℤ) (p:List Bool)
    (F:SupportedHistory S j p→ℝ) :
    (∑s:↥(S p),∑h:SupportedHistory S j p,if h.val.1=s.val then F h else 0)=∑h,F h := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  have hs : h.val.1∈S p :=
    mem_labels_range S h.property (root_mem_labels j p h.val.1 h.val.2)
  let s : ↥(S p) := ⟨h.val.1,hs⟩
  rw [Finset.sum_eq_single s]
  · simp [s]
  · intro s' hs' hne
    apply ite_eq_right
    intro he
    exact hne (Subtype.ext he.symm)
  · simp

theorem historyRootSum_total_norm_sq_le (k j:ℕ) (S:List Bool→Finset ℤ) (p:List Bool)
    (B V:(l:ℕ)→State k (l+1)→ℤ)
    (extra:(l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask:(l:ℕ)→ℤ→State k l→Prop) (X Δ W:ℝ) (x:State k j)
    (phase:ℤ→SupportedHistory S j p→ℂ) (hphase:∀s h,‖phase s h‖≤1) :
    (∑s:↥(S p),‖historyRootSum k j S p B V extra mask X Δ W s.val x (phase s.val)‖^2) ≤
      ∑h:SupportedHistory S j p,
        ‖retainedHistoryWeight k B V extra mask X Δ W j h.val.1 x h.val.2‖^2 := by
  calc
    _ ≤ ∑s:↥(S p),∑h:SupportedHistory S j p,if h.val.1=s.val then
        ‖retainedHistoryWeight k B V extra mask X Δ W j h.val.1 x h.val.2‖^2 else 0 :=
      Finset.sum_le_sum (fun s _=>historyRootSum_norm_sq_le k j S p B V extra mask X Δ W s.val x
        (phase s.val) (hphase s.val))
    _ = _ := sum_roots_history_indicators j S p _

end Ostmann.Characters.Template

end

end OAI
