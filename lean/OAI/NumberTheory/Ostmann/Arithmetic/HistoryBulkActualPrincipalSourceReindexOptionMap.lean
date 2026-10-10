import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionAlgebra

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

theorem option_div_of_map {α β : Type*} (x : Option α) (y : Option β)
    (f : α→β) (g : α→ℂ) (h : β→ℂ) (c : ℂ)
    (heq : ∀a,g a/c=h (f a)) (hmap : x.map f=y) :
    x.elim 0 g/c=y.elim 0 h :=
  (option_elim_div_map x f g h c heq).trans
    (congrArg (fun v : Option β=>v.elim 0 h) hmap)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
