import Mathlib
import OAI.Probability.UnimodularPercolation.Main
import OAI.Probability.UnimodularPercolation.Criticality.FullOperator

namespace OAI

/-! Threshold separation and simultaneous nonuniqueness under unimodularity. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

theorem main_unimodular [Infinite V] (G : BondGraph V E)
    (hinj : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) (x₀ : V)
    (hu : FullAutUnimodular G hinj hloc hconn x₀) : MainConclusion G := by
  let : TopologicalSpace V := ⊥
  let : DiscreteTopology V := ⟨rfl⟩
  apply mainConclusion_of_critical_bounded G hconn hloc hqt
  exact critical_bounded_of_graphUnimodular G hinj hconn hloc hqt hh x₀ hu

end Percolation

end OAI
