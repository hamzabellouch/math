import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexExchange
import OAI.NumberTheory.Ostmann.Construction.FiniteTransfer

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex
open Construction

theorem option_cmean_congr {α β : Type*} [Fintype α]
    (μ : FinitePrior α) (o : Option β) (f g : β → α → ℂ)
    (h : ∀r, μ.cmean (f r)=μ.cmean (g r)) :
    o.elim 0 (fun r=>μ.cmean (f r)) =
      μ.cmean (fun u=>o.elim 0 (fun r=>g r u)) :=
  (congrArg (o.elim (0:ℂ)) (funext h)).trans (option_cmean μ o g)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex

end

end OAI
