import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMeanChoicesDefs
import OAI.NumberTheory.Ostmann.Construction.SelectedCovarianceHistoryXi

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMean
open Construction

theorem outerPrior_cmean_assignment_first (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (F : OuterSample sources T giant → ℂ) :
    (outerPrior sources T giant).cmean F =
      (assignmentPrior sources T).cmean (fun x =>
        giant.law.cmean (fun p => giant.law.cmean (fun q => F (p,q,x)))) := by
  simp only [outerPrior,FinitePrior.pair_cmean]
  calc
    _ = giant.law.cmean (fun p => (assignmentPrior sources T).cmean (fun x =>
        giant.law.cmean (fun q => F (p,q,x)))) := by
      apply congrArg giant.law.cmean
      funext p
      exact FinitePrior.cmean_comm _ _ _
    _ = _ := FinitePrior.cmean_comm _ _ _

theorem pair_cmean_frequency_choices {A V I J : Type*}
    [Fintype A] [Fintype V] [Fintype I] [Fintype J]
    (μ : FinitePrior A) (w : I → J → ℂ) (F : A → A → V → I → J → ℂ) :
    μ.cmean (fun p => μ.cmean (fun q => ∑ v,∑ c,∑ e,w c e*F p q v c e)) =
      ∑ v,∑ c,∑ e,w c e*μ.cmean (fun p => μ.cmean (fun q => F p q v c e)) := by
  simp_rw [FinitePrior.cmean_sum,FinitePrior.cmean_mul_left]

end Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMean

end

end OAI
