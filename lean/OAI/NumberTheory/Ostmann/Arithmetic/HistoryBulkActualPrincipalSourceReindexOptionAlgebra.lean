import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

theorem option_elim_div_map {α β : Type*} (x : Option α) (f : α→β)
    (g : α→ℂ) (h : β→ℂ) (c : ℂ) (heq : ∀a,g a/c=h (f a)) :
    x.elim 0 g/c=(x.map f).elim 0 h :=
  Option.rec (zero_div c) (fun a=>heq a) x

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
