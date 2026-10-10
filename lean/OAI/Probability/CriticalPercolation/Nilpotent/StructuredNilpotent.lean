import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.DescentCritical
import OAI.Probability.CriticalPercolation.Nilpotent.NilpotentDescent

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph

theorem critical_null_of_nilpotent_quotient {V E Λ N : Type*}
    [Group Λ] [MulAction Λ V] [MulAction Λ E] [Group N] [Group.FG N] [Group.IsNilpotent N]
    (G : BondGraph V E) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hg : G.SubexponentialGrowth) (ha : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (ρ : Λ →* N) (hρ : Surjective ρ)
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite)
    (hpc : G.criticalProbability<1) : G.law G.criticalProbability G.percolates=0 :=
  critical_null_of_algebraic_descent (nilpotent_descent N) G hc hl hg ha S hS hcover
    ρ hρ hker hstab hpc

end CriticalPercolation.BondGraph
end
end
end

end OAI
