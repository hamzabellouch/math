import Mathlib

namespace OAI

namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

theorem option_map_elim_weight {α β : Type*} (o : Option α) (f : α → β)
    (w : α → ℝ) (F : β → ℝ → ℂ) :
    (o.map f).elim 0 (fun b=>F b (o.elim 0 w))=
      o.elim 0 (fun a=>F (f a) (w a)) := by
  cases o <;> rfl

theorem option_map_elim_weight_congr {α β : Type*}
    (o : Option α) (f : α → β) (w : α → ℝ) (F : β → ℝ → ℂ)
    (G : α → ℂ) (h : ∀a, F (f a) (w a)=G a) :
    (o.map f).elim 0 (fun b=>F b (o.elim 0 w))=o.elim 0 G := by
  cases o with
  | none => rfl
  | some a => exact h a

theorem option_kernel_mean_false {α β Ω : Type*}
    (M : (Ω → ℂ) → ℂ) (o : Option α) (f : α → β)
    (w : α → ℝ) (K : β → ℂ) (value : β → Ω → ℂ)
    (pred : Ω → Prop) [DecidablePred pred] (G : α → ℂ)
    (h : ∀a, K (f a) * M (fun u=>(w a:ℂ)*value (f a) u)=G a) :
    (o.map f).elim 0 (fun b=>K b*M (fun u=>((o.elim 0 w:ℝ):ℂ)*
      (if false ∧ pred u then 0 else value b u))) = o.elim 0 G := by
  cases o with
  | none => rfl
  | some a =>
    simpa only [Option.map_some, Option.elim_some, Bool.false_eq_true,
      false_and, ite_false] using h a

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end OAI
