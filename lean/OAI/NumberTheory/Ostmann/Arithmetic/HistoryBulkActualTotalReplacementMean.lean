import OAI.NumberTheory.Ostmann.Arithmetic.GiantCollisionError

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction

theorem norm_cmean_sub_le {α : Type*} [Fintype α] (μ : FinitePrior α)
    (f g : α → ℂ) (B : ℝ) (h : ∀ a, μ.mass a ≠ 0 → ‖f a-g a‖ ≤ B) :
    ‖μ.cmean f-μ.cmean g‖ ≤ B :=
  (congrArg norm (GiantCollisionError.cmean_sub_eq μ f g)).trans_le
    (GiantCollisionError.norm_cmean_le_of_mass_ne_zero μ _ B h)

theorem norm_cmean_sub_le_both {α : Type*} [Fintype α] (μ : FinitePrior α)
    (f g : α → ℂ) (B D : ℝ)
    (h : ∀ a, μ.mass a ≠ 0 → ‖f a-g a‖ ≤ B ∧ ‖f a-g a‖ ≤ D) :
    ‖μ.cmean f-μ.cmean g‖ ≤ B ∧ ‖μ.cmean f-μ.cmean g‖ ≤ D :=
  ⟨norm_cmean_sub_le μ f g B (fun a ha => (h a ha).1),
    norm_cmean_sub_le μ f g D (fun a ha => (h a ha).2)⟩

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
