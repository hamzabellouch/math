import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementMean

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction

theorem norm_guarded_cmean_sub_le_both {α : Type*} [Fintype α]
    (μ : FinitePrior α) (P : Prop) [Decidable P] (f g : P → α → ℂ)
    (B D : ℝ) (hB : 0≤B) (hD : 0≤D)
    (h : ∀hp : P,∀a,μ.mass a≠0→‖f hp a-g hp a‖≤B ∧ ‖f hp a-g hp a‖≤D) :
    ‖(if hp : P then μ.cmean (f hp) else 0)-(if hp : P then μ.cmean (g hp) else 0)‖≤B ∧
    ‖(if hp : P then μ.cmean (f hp) else 0)-(if hp : P then μ.cmean (g hp) else 0)‖≤D := by
  by_cases hp : P
  · simp only [dite_eq_left hp]
    exact norm_cmean_sub_le_both μ (f hp) (g hp) B D (h hp)
  · simpa only [dite_eq_right hp,sub_self,norm_zero] using And.intro hB hD

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
