import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedEvolution

namespace OAI

/-! The concrete fresh-row circuit preserves verifier acceptance exactly. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

abbrev qmaGridCircuit (c : QMACircuit) : QMACircuit :=
  ⟨qmaGridWork c.gates.length c.work,c.witness,
    qmaGridCircuitFrom c.gates.length c.work 0 c.gates (by omega)⟩

theorem qmaGridCircuit_wellFormed (c : QMACircuit) (hc : c.WellFormed) :
    (qmaGridCircuit c).WellFormed := by
  refine ⟨?_,qmaGridCircuitFrom_wellFormed _ _ _ _ _ hc.2⟩
  exact hc.1.trans (Nat.le_add_right _ _)

theorem qmaGridCircuit_length (c : QMACircuit) :
    (qmaGridCircuit c).gates.length = (3*(c.work+1)+1)*c.gates.length :=
  qmaGridCircuitFrom_length _ _ _ _ _

theorem qmaGridCircuit_size (c : QMACircuit) :
    (qmaGridCircuit c).work+(qmaGridCircuit c).gates.length =
      c.work+(4*c.work+5)*c.gates.length := by
  rw [qmaGridCircuit_length]
  change c.work+c.gates.length*(c.work+1)+(3*(c.work+1)+1)*c.gates.length = _
  ring

theorem qmaGridQubit_zero (rows width : ℕ) :
    qmaGridQubit rows width 0 = qmaPaddedLeft width (rows*(width+1)) := by
  funext i
  apply Fin.ext
  simp [qmaGridQubit]

theorem qmaWirePermutation_refl (n : ℕ) :
    qmaWirePermutation (qmaWireBasis (Equiv.refl (Fin n))) =
      (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) := by
  ext s t
  simp only [qmaWirePermutation,qmaWireBasis,Equiv.coe_fn_mk,Matrix.one_apply]
  rfl

theorem qmaGridCircuit_matrix (c : QMACircuit) :
    qmaCircuitMatrix (qmaGridCircuit c) =
      qmaWirePermutation (qmaWireBasis
        (qmaGridFrame c.gates.length c.work c.gates.length le_rfl))*
      qmaCircuitMatrix (qmaPaddedCircuit c (c.gates.length*(c.work+1))) := by
  change qmaGateProduct (qmaGridWork c.gates.length c.work)
      (qmaGridCircuitFrom c.gates.length c.work 0 c.gates _) =
    qmaWirePermutation (qmaWireBasis
      (qmaGridFrame c.gates.length c.work c.gates.length le_rfl))*
    qmaGateProduct (qmaGridWork c.gates.length c.work)
      (c.gates.map (qmaMapGate c.work (qmaGridWork c.gates.length c.work)
        (qmaPaddedLeft c.work (c.gates.length*(c.work+1)))))
  have h := qmaGridCircuitFrom_matrix c.gates.length c.work 0 c.gates (by omega)
  simpa only [qmaGridFrame,qmaWirePermutation_refl,mul_one,Nat.zero_add,qmaGridQubit_zero] using h

theorem qmaGridCircuit_output (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaOutputVector (qmaGridCircuit c) (qmaGridCircuit_wellFormed c hc) psi =
      qmaApplyMatrix (qmaWirePermutation (qmaWireBasis
        (qmaGridFrame c.gates.length c.work c.gates.length le_rfl)))
        (qmaOutputVector (qmaPaddedCircuit c (c.gates.length*(c.work+1)))
          (qmaPaddedCircuit_wellFormed c hc _) psi) := by
  change qmaApplyMatrix (qmaCircuitMatrix (qmaGridCircuit c))
      (qmaInputVector (qmaPaddedCircuit c (c.gates.length*(c.work+1)))
        (qmaPaddedCircuit_wellFormed c hc _) psi) = _
  rw [qmaGridCircuit_matrix,qmaApplyMatrix_mul]
  rfl

theorem qmaGridFrame_output (c : QMACircuit) :
    (qmaGridFrame c.gates.length c.work c.gates.length le_rfl).symm
      (qmaPaddedLeft c.work (c.gates.length*(c.work+1)) (Fin.last c.work)) =
      Fin.last (qmaGridWork c.gates.length c.work) := by
  rw [←qmaGridQubit_zero,qmaGridFrame_active]
  apply Fin.ext
  change c.gates.length*(c.work+1)+c.work = c.work+c.gates.length*(c.work+1)
  omega

theorem qmaGridCircuit_acceptance (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaAcceptance (qmaGridCircuit c) (qmaGridCircuit_wellFormed c hc) psi =
      qmaAcceptance c hc psi := by
  rw [qmaAcceptance_projection (qmaGridCircuit c) (qmaGridCircuit_wellFormed c hc) psi,
    qmaAcceptance_projection c hc psi,qmaGridCircuit_output c hc psi]
  rw [←qmaGridFrame_output]
  rw [qmaWirePermutation_probability]
  exact qmaPaddedOutput_probability c hc _ psi (Fin.last c.work) 1

end ContinuumCoulomb

end

end OAI
