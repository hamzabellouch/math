import Mathlib.Data.Option.Basic

namespace OAI

namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

theorem option_match_eq_elim {α β : Type*} (r : Option α) (z : β) (F : α → β) :
    (match r with | none => z | some a => F a) = r.elim z F := by
  cases r <;> rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end OAI
