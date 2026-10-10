import OAI.NumberTheory.Ostmann.Construction.OffDiagonalExpectations

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

theorem sum_eq_of_pointwise {ι : Type*} [Fintype ι]
    (F G : ι → ℂ) (z : ℂ) (h : ∀i,F i=G i) (hg : (∑i,G i)=z) :
    (∑i,F i)=z :=
  (Finset.sum_congr rfl (fun i _=>h i)).trans hg

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
