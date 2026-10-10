import Mathlib.Basic.Complex.Basic

namespace OAI

namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

theorem option_elim_mul {β : Type*} (r : Option β) (c : ℂ) (F : β → ℂ) :
    r.elim 0 (fun b=>c*F b)=c*r.elim 0 F := by
  cases r <;> simp only [Option.elim_none,Option.elim_some,mul_zero]

theorem option_elim_mul_of_eq {β : Type*} (r : Option β) (c : ℂ)
    (F G : β → ℂ) (h : ∀b,F b=c*G b) :
    r.elim 0 F=c*r.elim 0 G := by
  cases r with
  | none => exact (mul_zero c).symm
  | some b => exact h b

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end OAI
