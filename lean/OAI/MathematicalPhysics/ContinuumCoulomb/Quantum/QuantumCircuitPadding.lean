import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialXZBounds

namespace OAI

/-! Two cancelling Hadamards remove the empty-circuit exception without changing acceptance. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaHadamard_selfAdjoint : qmaHadamard.conjTranspose = qmaHadamard := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [qmaHadamard,Matrix.conjTranspose_apply,bellScale_star]

theorem qmaHadamard_square : qmaHadamard*qmaHadamard = 1 := by
  simpa only [qmaHadamard_selfAdjoint] using qmaHadamard_gram

theorem qmaGateMatrix_hadamard_square (work i : ℕ) :
    qmaGateMatrix work (.hadamard i)*qmaGateMatrix work (.hadamard i) = 1 := by
  change sourceTensor _ _*sourceTensor _ _ = _
  rw [sourceTensor_mul,← sourceTensor_one (work+1)]
  congr 1
  funext k
  split_ifs <;> simp [qmaHadamard_square]

def qmaNonemptyCircuit (c : QMACircuit) : QMACircuit :=
  ⟨c.work,c.witness,c.gates++[.hadamard 0,.hadamard 0]⟩

theorem qmaNonemptyCircuit_wellFormed (c : QMACircuit) (hc : c.WellFormed) :
    (qmaNonemptyCircuit c).WellFormed := by
  refine ⟨hc.1,?_⟩
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hc.2 g hg
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl <;> exact Nat.succ_pos _

theorem qmaNonemptyCircuit_matrix (c : QMACircuit) :
    qmaCircuitMatrix (qmaNonemptyCircuit c) = qmaCircuitMatrix c := by
  change qmaGateProduct c.work (c.gates++[.hadamard 0,.hadamard 0]) = _
  rw [qmaGateProduct_append]
  have hh : qmaGateProduct c.work [.hadamard 0,.hadamard 0] = 1 := by
    simpa only [qmaGateProduct,qmaCircuitMatrix,List.foldl_cons,List.foldl_nil,mul_one] using
      qmaGateMatrix_hadamard_square c.work 0
  rw [hh,one_mul]
  rfl

theorem qmaNonemptyCircuit_acceptance (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaAcceptance (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc) psi =
      qmaAcceptance c hc psi := by
  unfold qmaAcceptance
  rw [qmaNonemptyCircuit_matrix]
  rfl

theorem qmaNonemptyCircuit_length (c : QMACircuit) :
    (qmaNonemptyCircuit c).gates.length = c.gates.length+2 := by
  simp [qmaNonemptyCircuit]

theorem qmaNonemptyCircuit_nearest (c : QMACircuit) :
    (qmaNearestCircuit (qmaNonemptyCircuit c)).gates ≠ [] := by
  simp [qmaNonemptyCircuit,List.flatMap_append,qmaNearestGate]

theorem qmaNonemptyCircuit_sparse_pos (c : QMACircuit) :
    0 < (qmaSparseCircuit (qmaNonemptyCircuit c)).gates.length := by
  have hn := List.length_pos_iff.mpr (qmaNonemptyCircuit_nearest c)
  change 0 < (qmaSweepCircuitFrom _ _ 0 _ _).length
  rw [qmaSweepCircuitFrom_length]
  exact Nat.mul_pos (by omega) hn

end ContinuumCoulomb

end

end OAI
