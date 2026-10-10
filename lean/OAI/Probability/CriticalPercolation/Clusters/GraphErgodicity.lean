import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.AutDisplacement
import OAI.Probability.CriticalPercolation.GraphGeometry.UniformGeometry
import OAI.Probability.CriticalPercolation.ProductMeasure.BernoulliErgodicity

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem invariant_event_zero_one [Infinite V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (p : unitInterval)
    (A : Set (Set E)) (hA : MeasurableSet A)
    (hinv : ∀ φ : G.Aut, (fun ω : Set E => φ.edge '' ω) ⁻¹' A = A) :
    G.law p A = 0 ∨ G.law p A = 1 := by
  have hh := BernoulliProduct.invariant_zero_one p (fun φ : G.Aut => (Aut.symm G φ).edge)
    (fun S => by
      obtain ⟨φ,hφ⟩ := G.aut_displaces_finite_bonds hc hl hq (S : Set E) S.finite_toSet
      exact ⟨φ,hφ⟩) A hA (fun φ => hinv (Aut.symm G φ))
  simpa only [BernoulliProduct.law_const,law] using hh

end CriticalPercolation.BondGraph
end
end

end OAI
