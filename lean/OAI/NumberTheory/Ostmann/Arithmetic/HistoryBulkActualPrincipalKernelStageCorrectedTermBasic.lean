import Mathlib.Data.Option.Basic

namespace OAI

namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

theorem option_dite_get_eq_elim_inst {α β : Type*} (r : Option α) (z : β)
    [Decidable (r.isSome = true)]
    (F : (h : r.isSome) → β) (G : α → β)
    (hFG : ∀h, F h = G (r.get h)) :
    (if h : r.isSome then F h else z) = r.elim z G := by
  cases r with
  | none => simp only [Option.isSome_none,Bool.false_eq_true,dite_false,Option.elim_none]
  | some a => simpa only [Option.isSome_some,dite_true,Option.get_some,Option.elim_some] using hFG rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end OAI
