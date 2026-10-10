import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZFamilySplit
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBlockFull

namespace OAI

/-! The full X/Z family is simulated in the ordinary physical qubit space. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

def qmaXZBlockBudget (t : κ → QMAXZTerm n) (J : κ → ℝ) : ℝ :=
  qmaFourTensorFullBudget (fun e : QMAXZPairIndex t => J e.val)
    (fun e : QMAXZFieldIndex t => J e.val) (qmaXZFamilyConstant t J)

def qmaXZBlockSource (r : ℝ) (t : κ → QMAXZTerm n) (J : κ → ℝ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  qmaBlockSourceFull r
    (fun e => (qmaXZPairData t e).left) (fun e => (qmaXZPairData t e).right)
    (fun e => (qmaXZPairData t e).axisLeft) (fun e => (qmaXZPairData t e).axisRight)
    (fun e => J e.val)
    (fun e => (qmaXZFieldData t e).site) (fun e => (qmaXZFieldData t e).axis)
    (fun e => J e.val) (qmaXZFamilyConstant t J)

theorem qmaXZBlock_accuracy (t : κ → QMAXZTerm n) (J : κ → ℝ)
    (hprivate : ∀ e f, (qmaPauliSupport (t e).word).card = 2 →
      qmaPauliSupport (t e).word = qmaPauliSupport (t f).word → e = f)
    (N : ℕ) (hN : 0 < N) :
    |MediatorGraph.normalizedBottom (qmaXZBlockSource (9*(qmaXZBlockBudget t J)^3*N) t J)-
      MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • (t e).matrix)| ≤ 1/(N:ℝ) := by
  have h := qmaBlockSourceFull_accuracy
    (fun e => (qmaXZPairData t e).left) (fun e => (qmaXZPairData t e).right)
    (fun e => (qmaXZPairData t e).axisLeft) (fun e => (qmaXZPairData t e).axisRight)
    (fun e => J e.val)
    (fun e => (qmaXZPairData t e).distinct)
    (fun e f hef => qmaXZPairData_distinct t hprivate e f hef)
    (fun e => (qmaXZFieldData t e).site) (fun e => (qmaXZFieldData t e).axis)
    (fun e => J e.val) (qmaXZFamilyConstant t J) N hN
  rw [qmaXZFamily_target] at h
  exact h

theorem qmaXZWords_heisenberg (w : κ → Fin n → Fin 4) (J : κ → ℝ)
    (hy : ∀ e i, w e i ≠ 2) (hw : ∀ e, (qmaPauliSupport (w e)).card ≤ 2)
    (hprivate : ∀ e f, (qmaPauliSupport (w e)).card = 2 →
      qmaPauliSupport (w e) = qmaPauliSupport (w f) → e = f)
    (N : ℕ) (hN : 0 < N) :
    ∃ t : κ → QMAXZTerm n, (∀ e, (t e).word = w e) ∧
      |MediatorGraph.normalizedBottom (qmaXZBlockSource (9*(qmaXZBlockBudget t J)^3*N) t J)-
        MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • qmaPauliWord (w e))| ≤ 1/(N:ℝ) := by
  choose t ht using fun e => qmaXZWord_term (w e) (hy e) (hw e)
  refine ⟨t,ht,?_⟩
  have hp : ∀ e f, (qmaPauliSupport (t e).word).card = 2 →
      qmaPauliSupport (t e).word = qmaPauliSupport (t f).word → e = f := by
    simpa only [ht] using hprivate
  have hm : ∀ e, (t e).matrix = qmaPauliWord (w e) := by
    intro e
    rw [← QMAXZTerm.word_matrix,ht]
  simpa only [hm] using qmaXZBlock_accuracy t J hp N hN

end ContinuumCoulomb

end

end OAI
