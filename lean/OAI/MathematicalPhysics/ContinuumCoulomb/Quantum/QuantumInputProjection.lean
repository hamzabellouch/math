import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSoundness

namespace OAI

/-! The legal initial subspace is exactly the zero-ancilla witness embedding. -/

noncomputable section
namespace ContinuumCoulomb

def qmaExtractWitness (c : QMACircuit)
    (u : EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    EuclideanSpace ℂ (SourceSpinBasis c.witness) :=
  WithLp.toLp 2 (fun s => u (qmaWitnessExtend c s))

theorem qmaInputVector_extract (c : QMACircuit) (hc : c.WellFormed)
    (u : EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    qmaInputVector c hc (qmaExtractWitness c u) = qmaMask (QMAAncillaZero c) u := by
  classical
  ext s
  by_cases hs : QMAAncillaZero c s
  · have hs' : ∀ i : Fin (c.work+1), c.witness ≤ i.val → s i = 0 := hs
    simp only [qmaInputVector,qmaInitialState,PiLp.toLp_apply,ite_eq_left hs',
      qmaExtractWitness,qmaMask_apply,ite_eq_left hs]
    change u (qmaWitnessExtend c (qmaWitnessRestrict c hc s)) = u s
    rw [qmaWitnessExtend_restrict c hc s hs]
  · have hs' : ¬∀ i : Fin (c.work+1), c.witness ≤ i.val → s i = 0 := hs
    simp only [qmaInputVector,qmaInitialState,PiLp.toLp_apply,ite_eq_right hs',
      qmaMask_apply,ite_eq_right hs]

theorem qmaExtractWitness_norm (c : QMACircuit) (hc : c.WellFormed)
    (u : EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    ‖qmaExtractWitness c u‖ = ‖qmaMask (QMAAncillaZero c) u‖ := by
  rw [←qmaInputVector_extract c hc u,qmaInputVector_norm]

end ContinuumCoulomb

end

end OAI
