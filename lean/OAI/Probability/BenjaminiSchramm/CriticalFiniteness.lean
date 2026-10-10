import OAI.Probability.BenjaminiSchramm.PhaseInput
import OAI.Probability.CriticalPercolation.Criticality.LayerContradiction

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem criticalModel_percolates (G : BondGraph V E) :
    (criticalModel G).percolates = {ω | (infiniteClusters G ω).Nonempty} := by
  ext ω
  simp only [CriticalPercolation.BondGraph.percolates, Set.mem_ofPred_eq,
    criticalModel_cluster, Set.Nonempty, infiniteClusters]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨cluster G ω x,hx,x,rfl⟩
  · rintro ⟨C,hC,x,hx⟩
    exact ⟨x,hx ▸ hC⟩

theorem criticalModel_pc (G : BondGraph V E) :
    (criticalModel G).criticalProbability = pc G := by
  simp only [CriticalPercolation.BondGraph.criticalProbability, criticalModel_percolates,
    CriticalPercolation.BondGraph.law, pc, law]

theorem critical_finite_of_combinatorial_nonunimodular [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hpc : pc G < 1)
    (hu : ¬ (criticalModel G).CombinatoriallyUnimodular) (x : V) :
    ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite := by
  have hz := (criticalModel G).nonunimodular_no_percolation_at_criticality
    (criticalModel_connected G hconn) hloc (criticalModel_quasiTransitive G hqt) hu
    (by simpa only [criticalModel_pc] using hpc)
  rw [criticalModel_pc, criticalModel_percolates] at hz
  change law (pc G) {ω | (infiniteClusters G ω).Nonempty} = 0 at hz
  rw [ae_iff]
  apply measure_mono_null _ hz
  intro ω hω
  exact ⟨cluster G ω x,hω,x,rfl⟩

end Percolation.BenjaminiSchramm

end OAI
