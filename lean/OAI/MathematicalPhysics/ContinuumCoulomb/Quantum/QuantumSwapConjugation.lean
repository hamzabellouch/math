import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridAcceptance

namespace OAI

/-! Exact conjugation by the three-CNOT adjacent-swap program. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

def qmaOrderedCnot (i j : ℕ) (forward : Bool) : QMAGate :=
  if forward then .controlledNot i j else .controlledNot j i

theorem qmaWireSwap_conjugate {work : ℕ} (i j : Fin (work+1)) (hij : i ≠ j)
    (g : QMAGate) :
    qmaGateProduct work (qmaWireSwapGates i j)*qmaGateMatrix work g*
      qmaGateProduct work (qmaWireSwapGates i j) =
        qmaGateMatrix work (qmaRelabelGate work (Equiv.swap i j) g) := by
  have hm : qmaGateProduct work (qmaWireSwapGates i j) =
      qmaWirePermutation (qmaWireBasis (Equiv.swap i j)) := qmaWireSwap_matrix i j hij
  rw [hm]
  rw [qmaGate_wire_intertwines,Equiv.symm_swap,mul_assoc,qmaWireBasis_product,
    Equiv.swap_swap,qmaWirePermutation_refl,mul_one]

theorem qmaSwap_relabels_ordered {work : ℕ} (i j k : Fin (work+1))
    (hki : k ≠ i) (hkj : k ≠ j) (forward : Bool) :
    qmaRelabelGate work (Equiv.swap i j) (qmaOrderedCnot j.val k.val forward) =
      qmaOrderedCnot i.val k.val forward := by
  cases forward <;>
    simp [qmaOrderedCnot,qmaRelabelGate,qmaQubit_fin,
      Equiv.swap_apply_of_ne_of_ne hki hkj]

end ContinuumCoulomb

end

end OAI
