import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumWireSwap

namespace OAI

/-! Exact sequential products for the circuit transformations used by the sparse history. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix

abbrev qmaGateProduct (work : ℕ) (gs : List QMAGate) :
    Matrix (SourceSpinBasis (work+1)) (SourceSpinBasis (work+1)) ℂ :=
  qmaCircuitMatrix ⟨work,0,gs⟩

theorem qmaGateProduct_fold (work : ℕ) (gs : List QMAGate)
    (M : Matrix (SourceSpinBasis (work+1)) (SourceSpinBasis (work+1)) ℂ) :
    gs.foldl (fun A g => qmaGateMatrix work g*A) M = qmaGateProduct work gs*M := by
  induction gs generalizing M with
  | nil => simp [qmaGateProduct,qmaCircuitMatrix]
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    change _ = gs.foldl (fun A g => qmaGateMatrix work g*A) (qmaGateMatrix work g*1)*M
    rw [ih]
    simp only [mul_one,mul_assoc]

theorem qmaGateProduct_append (work : ℕ) (xs ys : List QMAGate) :
    qmaGateProduct work (xs++ys) = qmaGateProduct work ys*qmaGateProduct work xs := by
  change (xs++ys).foldl _ 1 = _
  rw [List.foldl_append,qmaGateProduct_fold]
  rfl

theorem qmaGateProduct_singleton (work : ℕ) (g : QMAGate) :
    qmaGateProduct work [g] = qmaGateMatrix work g := by
  simp [qmaGateProduct,qmaCircuitMatrix]

theorem qmaGateProduct_nil (work : ℕ) : qmaGateProduct work [] = 1 := rfl

end ContinuumCoulomb

end

end OAI
