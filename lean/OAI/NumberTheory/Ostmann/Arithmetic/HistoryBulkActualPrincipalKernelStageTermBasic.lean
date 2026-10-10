import Mathlib.Data.Option.Basic

namespace OAI

namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

theorem option_match_get {α β : Type*} (r : Option α) (z : β) (F : α → β)
    (h : r.isSome) :
    r.elim z F = F (r.get h) := by
  cases r with
  | none => cases h
  | some a => rfl

theorem option_dite_get_eq_elim {α β : Type*} (r : Option α) [Decidable (r.isSome)] (z : β)
    (F : (h : r.isSome) → β) (G : α → β)
    (hFG : ∀h, F h = G (r.get h)) :
    (if h : r.isSome then F h else z) = r.elim z G := by
  cases r with
  | none => simp only [Option.isSome_none,Bool.false_eq_true,dite_false,Option.elim_none]
  | some a =>
    simp only [Option.isSome_some,dite_true,Option.elim_some]
    exact hFG rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

end OAI
