import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.StructuredNilpotent
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteIndexAction

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph

theorem critical_null_of_virtually_nilpotent_quotient {V E Λ Q : Type*}
    [Group Λ] [MulAction Λ V] [MulAction Λ E] [Group Q] [Group.FG Q]
    (G : BondGraph V E) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hg : G.SubexponentialGrowth) (ha : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (ρ : Λ →* Q) (hρ : Surjective ρ)
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set Q).Finite)
    (N : Subgroup Q) [Group.IsNilpotent N] (hN : N.index≠0)
    (hpc : G.criticalProbability<1) : G.law G.criticalProbability G.percolates=0 := by
  let _ : N.FiniteIndex := ⟨hN⟩
  obtain ⟨ha',⟨R,hR,hRcover⟩,hsur,hfinite,hst⟩ :=
    G.finiteIndex_quotient_transfer ha S hS hcover ρ hρ hker hstab N hN
  exact critical_null_of_nilpotent_quotient G hc hl hg ha' R hR hRcover
    (quotientSubgroupMap ρ N) hsur hfinite hst hpc

end CriticalPercolation.BondGraph
end
end
end

end OAI
