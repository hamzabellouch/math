import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Criticality.MainSparseBoundary
import OAI.Probability.CriticalPercolation.Modular.ModularLevelGeometry
import OAI.Probability.CriticalPercolation.Nilpotent.StructuredVirtuallyNilpotent

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem critical_null_of_normal_nilpotent_model
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hg : G.SubexponentialGrowth)
    (Λ : Subgroup G.Aut) [Group.FG Λ]
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (K : Subgroup Λ) [K.Normal]
    (hker : ∀ v : V, (MulAction.orbit K v).Finite)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map (QuotientGroup.mk' K) :
      Set (Λ ⧸ K)).Finite)
    (N : Subgroup (Λ ⧸ K)) [Group.IsNilpotent N] (hN : N.index≠0)
    (hpc : G.criticalProbability<1) : G.law G.criticalProbability G.percolates=0 := by
  let _ : MulAction G.Aut E := G.autEdgeAction
  apply G.critical_null_of_virtually_nilpotent_quotient hc hl hg
    (G.subgroup_preservesEnds G.aut_preservesEnds Λ) S hS hcover
    (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) _ hstab N hN hpc
  intro v
  apply (hker v).subset
  rintro w ⟨g,rfl⟩
  have hg : g.val∈K := by simpa only [QuotientGroup.ker_mk'] using g.property
  exact ⟨⟨g.val,hg⟩,rfl⟩

theorem main_failure_excludes_normal_nilpotent_model [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1)
    (hper : G.law G.criticalProbability G.percolates≠0)
    (Λ : Subgroup G.Aut) [Group.FG Λ]
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (K : Subgroup Λ) [K.Normal]
    (hker : ∀ v : V, (MulAction.orbit K v).Finite)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map (QuotientGroup.mk' K) :
      Set (Λ ⧸ K)).Finite)
    (N : Subgroup (Λ ⧸ K)) [Group.IsNilpotent N] (hN : N.index≠0) : False := by
  have hg := (G.main_failure_sparse_polynomial hc hl hq hpc hper).1
  exact hper (G.critical_null_of_normal_nilpotent_model hc hl hg Λ S hS hcover K hker hstab N hN hpc)

end CriticalPercolation.BondGraph
end
end

end OAI
