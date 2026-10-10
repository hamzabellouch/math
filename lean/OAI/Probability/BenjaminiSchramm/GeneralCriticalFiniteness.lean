import OAI.Probability.BenjaminiSchramm.CriticalFiniteness
import OAI.Probability.CriticalPercolation.Main

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem critical_finite_general [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hpc : pc G < 1) (x : V) :
    ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite := by
  have hz := (criticalModel G).no_percolation_at_criticality
    (criticalModel_connected G hconn) hloc (criticalModel_quasiTransitive G hqt)
    (by simpa only [criticalModel_pc] using hpc)
  rw [criticalModel_pc,criticalModel_percolates] at hz
  change law (pc G) {ω | (infiniteClusters G ω).Nonempty} = 0 at hz
  rw [ae_iff]
  apply measure_mono_null _ hz
  intro ω hω
  exact ⟨cluster G ω x,hω,x,rfl⟩

end Percolation.BenjaminiSchramm

end OAI
