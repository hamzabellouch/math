import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Lagrangian
import OAI.Analysis.MatrixSigning.Matrices.InnerRight

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

def SymmetricMap (η : H d →L[ℝ] H d) : Prop :=
  ∀ A B, inner ℝ A (η B) = inner ℝ (η A) B

lemma lagrangian_separate (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (hη : SymmetricMap η) (P Q : H d) (z : Point d) :
    lagrangian ε S η P Q z =
      z.1 * (1-realTrace P-realTrace Q) + (inner ℝ P S - inner ℝ Q S) +
        (inner ℝ P (invH z.2.1) + inner ℝ (η Q + ε • Hermitian.one) z.2.1) +
        (inner ℝ Q (invH z.2.2) + inner ℝ (η P + ε • Hermitian.one) z.2.2) := by
  simp only [lagrangian, objective, residual, inner_add_right, inner_sub_right,
    inner_add_left, inner_smul_rightH, inner_smul_leftH, inner_right_one,
    inner_one, realTrace_add, hη P z.2.2, hη Q z.2.1]
  ring

lemma stationary_trace (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (hη : SymmetricMap η) (P Q : H d) (z : Point d) (hz : z ∈ domain d)
    (hmin : ∀ w ∈ domain d, lagrangian ε S η P Q z ≤ lagrangian ε S η P Q w) :
    realTrace P + realTrace Q = 1 := by
  have hp := hmin (z.1+1,z.2) hz
  have hm := hmin (z.1-1,z.2) hz
  rw [lagrangian_separate ε S η hη, lagrangian_separate ε S η hη] at hp hm
  dsimp only at hp hm
  nlinarith

lemma stationary_X [NeZero d] (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (hη : SymmetricMap η) (P Q : H d) (z : Point d) (hz : z ∈ domain d)
    (hmin : ∀ w ∈ domain d, lagrangian ε S η P Q z ≤ lagrangian ε S η P Q w) :
    sandwich (invH z.2.1) P = η Q + ε • (Hermitian.one : H d) := by
  apply inverse_trace_stationarity P _ _ hz.1
  intro X hX
  have h := hmin (z.1,X,z.2.2) ⟨hX,hz.2⟩
  rw [lagrangian_separate ε S η hη, lagrangian_separate ε S η hη] at h
  dsimp only at h
  linarith

lemma stationary_Y [NeZero d] (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (hη : SymmetricMap η) (P Q : H d) (z : Point d) (hz : z ∈ domain d)
    (hmin : ∀ w ∈ domain d, lagrangian ε S η P Q z ≤ lagrangian ε S η P Q w) :
    sandwich (invH z.2.2) Q = η P + ε • (Hermitian.one : H d) := by
  apply inverse_trace_stationarity Q _ _ hz.2
  intro Y hY
  have h := hmin (z.1,z.2.1,Y) ⟨hz.1,hY⟩
  rw [lagrangian_separate ε S η hη, lagrangian_separate ε S η hη] at h
  dsimp only at h
  linarith

end
end CurrentKS.Variational

end OAI
