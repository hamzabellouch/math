import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEvolution
import Mathlib.Data.List.TakeDrop

namespace OAI

/-! Exact circuit prefixes and their unitary changes of coordinates. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix

@[simp] theorem qmaApplyMatrix_one {n : ℕ} (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    qmaApplyMatrix 1 u = u := by
  ext s
  simp [qmaApplyMatrix]

theorem qmaApplyMatrix_mul {n : ℕ}
    (M N : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    qmaApplyMatrix (M*N) u = qmaApplyMatrix M (qmaApplyMatrix N u) := by
  ext s
  simp [qmaApplyMatrix,Matrix.mulVec_mulVec]

theorem qmaApplyMatrix_sub {n : ℕ}
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (u w : EuclideanSpace ℂ (SourceSpinBasis n)) :
    qmaApplyMatrix M (u-w) = qmaApplyMatrix M u-qmaApplyMatrix M w := by
  ext s
  change (M.mulVec ((fun s => u s)-(fun s => w s))) s = _
  rw [Matrix.mulVec_sub]
  rfl

def qmaPrefixMatrix (c : QMACircuit) (t : ℕ) :
    Matrix (SourceSpinBasis (c.work+1)) (SourceSpinBasis (c.work+1)) ℂ :=
  (c.gates.take t).foldl (fun M g => qmaGateMatrix c.work g*M) 1

@[simp] theorem qmaPrefixMatrix_zero (c : QMACircuit) : qmaPrefixMatrix c 0 = 1 := rfl

@[simp] theorem qmaPrefixMatrix_length (c : QMACircuit) :
    qmaPrefixMatrix c c.gates.length = qmaCircuitMatrix c := by
  simp [qmaPrefixMatrix,qmaCircuitMatrix]

theorem qmaPrefixMatrix_gram (c : QMACircuit) (hc : c.WellFormed) (t : ℕ) :
    (qmaPrefixMatrix c t).conjTranspose*qmaPrefixMatrix c t = 1 := by
  let d : QMACircuit := { c with gates := c.gates.take t }
  have hd : d.WellFormed := ⟨hc.1,fun g hg => hc.2 g (List.mem_of_mem_take hg)⟩
  exact qmaCircuitMatrix_gram d hd

theorem qmaPrefixMatrix_cogram (c : QMACircuit) (hc : c.WellFormed) (t : ℕ) :
    qmaPrefixMatrix c t*(qmaPrefixMatrix c t).conjTranspose = 1 :=
  mul_eq_one_comm.mp (qmaPrefixMatrix_gram c hc t)

def qmaStepMatrix (c : QMACircuit) (t : ℕ) :
    Matrix (SourceSpinBasis (c.work+1)) (SourceSpinBasis (c.work+1)) ℂ :=
  qmaGateMatrix c.work (c.gates.getD t (.hadamard 0))

theorem qmaPrefixMatrix_succ (c : QMACircuit) (t : ℕ) (ht : t < c.gates.length) :
    qmaPrefixMatrix c (t+1) = qmaStepMatrix c t*qmaPrefixMatrix c t := by
  unfold qmaPrefixMatrix qmaStepMatrix
  rw [←List.take_concat_get' c.gates t ht,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [List.getD_eq_get c.gates (.hadamard 0) ⟨t,ht⟩]
  rfl

theorem qmaStepMatrix_gram (c : QMACircuit) (hc : c.WellFormed)
    (t : ℕ) (ht : t < c.gates.length) :
    (qmaStepMatrix c t).conjTranspose*qmaStepMatrix c t = 1 := by
  apply qmaGateMatrix_gram
  rw [List.getD_eq_get c.gates (.hadamard 0) ⟨t,ht⟩]
  exact hc.2 _ (List.get_mem _ _)

end ContinuumCoulomb

end

end OAI
