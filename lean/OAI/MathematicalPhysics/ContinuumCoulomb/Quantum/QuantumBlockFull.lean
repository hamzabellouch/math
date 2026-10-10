import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBlockHamiltonian
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorFullFamily

namespace OAI

/-! The full physical simulator as a sum of ordinary Heisenberg exchanges. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

def qmaBlockSourceCounterterm (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  qmaBlockSourceAxisField i a (qmaFourCounterA a b t)+
    qmaBlockSourceAxisField j b (qmaFourCounterB a b t)

theorem qmaBlockSourceCounterterm_reindex (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    (qmaBlockSourceCounterterm i j a b t).submatrix
      (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm = qmaFourTensorCounterterm i j a b t := by
  simp only [qmaBlockSourceCounterterm,MediatorGraph.submatrix_add_apply,
    qmaBlockSourceAxisField_reindex,qmaFourTensorCounterterm]

def qmaBlockSourceOnsite (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  (∑ e, qmaBlockSourceAxisField (site e) (axis e) (weight e))+
    ((constant-qmaFourTensorFieldShift axis weight:ℝ):ℂ) • 1

theorem qmaBlockSourceOnsite_reindex (site : τ → Fin n) (axis : τ → Fin 2)
    (weight : τ → ℝ) (constant : ℝ) :
    (qmaBlockSourceOnsite site axis weight constant).submatrix
      (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm =
      qmaFourTensorOnsite site axis weight constant := by
  simp only [qmaBlockSourceOnsite,MediatorGraph.submatrix_add_apply,
    MediatorGraph.submatrix_sum,qmaBlockSourceAxisField_reindex,
    MediatorGraph.submatrix_smul_apply,Matrix.submatrix_one_equiv,
    qmaFourTensorOnsite,qmaFourTensorFields]

def qmaBlockSourceFull (r : ℝ) (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  ((r^2:ℝ):ℂ) • qmaBlockSourcePenalty n+
    (r:ℂ) • (∑ e, qmaBlockSourceCoupling (left e) (right e) (a e) (b e) (t e))+
    (∑ e, qmaBlockSourceCounterterm (left e) (right e) (a e) (b e) (t e))+
    qmaBlockSourceOnsite site axis weight constant

theorem qmaBlockSourceFull_reindex (r : ℝ) (left right : κ → Fin n)
    (a b : κ → Fin 2) (t : κ → ℝ) (hneq : ∀ e, left e ≠ right e)
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) :
    (qmaBlockSourceFull r left right a b t site axis weight constant).submatrix
      (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm =
      qmaFourTensorPhysicalMatrix r
        ((r:ℂ) • qmaFourTensorFamilyCoupling left right a b t+
          qmaFourTensorFullCounterterm left right a b t site axis weight constant) := by
  simp only [qmaBlockSourceFull,MediatorGraph.submatrix_add_apply,
    MediatorGraph.submatrix_smul_apply,MediatorGraph.submatrix_sum,qmaBlockSourcePenalty_reindex,
    qmaBlockSourceCoupling_reindex _ _ (hneq _),qmaBlockSourceCounterterm_reindex,
    qmaBlockSourceOnsite_reindex,qmaFourTensorPhysicalMatrix,qmaFourTensorFamilyCoupling,
    qmaFourTensorFullCounterterm,qmaFourTensorFamilyCounterterm,Complex.ofReal_pow]
  abel

theorem qmaBlockSourceFull_accuracy (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e)
    (hdist : ∀ e f, e ≠ f → ({left e,right e} : Finset (Fin n)) ≠ {left f,right f})
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) (N : ℕ) (hN : 0 < N) :
    |MediatorGraph.normalizedBottom (qmaBlockSourceFull
        (9*(qmaFourTensorFullBudget t weight constant)^3*N)
        left right a b t site axis weight constant)-
      MediatorGraph.normalizedBottom (qmaFourTensorFullTarget left right a b t site axis weight constant)| ≤
        1/(N:ℝ) := by
  have h := qmaFourTensorFull_accuracy left right a b t hneq hdist site axis weight constant N hN
  rw [← qmaBlockSourceFull_reindex _ left right a b t hneq site axis weight constant,
    MediatorGraph.normalizedBottom_reindex] at h
  exact h

end ContinuumCoulomb

end

end OAI
