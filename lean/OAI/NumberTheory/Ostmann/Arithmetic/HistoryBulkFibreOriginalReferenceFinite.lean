import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkFibreOriginalReference
open Construction

theorem cmean_frequency_choices {A V I J : Type*}
    [Fintype A] [Fintype V] [Fintype I] [Fintype J]
    (μ : FinitePrior A) (w : I → J → ℂ) (F : A → V → I → J → ℂ) :
    μ.cmean (fun x => ∑v,∑c,∑e,w c e*F x v c e) =
      ∑v,∑c,∑e,w c e*μ.cmean (fun x => F x v c e) := by
  simp_rw [FinitePrior.cmean_sum,FinitePrior.cmean_mul_left]

end Ostmann.Arithmetic.HistoryBulkFibreOriginalReference

end

end OAI
