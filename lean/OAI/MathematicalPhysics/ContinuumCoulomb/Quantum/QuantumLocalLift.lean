import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRealCircuit
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace OAI

/-! Exact tensor-local operators, with explicit finite supports. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev QMASupportBasis (S : Finset ι) := (i : {i // i ∈ S}) → Fin 2
abbrev QMASpectatorBasis (S : Finset ι) := (i : {i // i ∉ S}) → Fin 2

def qmaSupportSplit (S : Finset ι) :
    (ι → Fin 2) ≃ QMASupportBasis S × QMASpectatorBasis S :=
  Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Fin 2)

def qmaLocalLift (S : Finset ι) (A : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) :
    Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  (A ⊗ₖ (1 : Matrix (QMASpectatorBasis S) (QMASpectatorBasis S) ℂ)).submatrix
    (qmaSupportSplit S) (qmaSupportSplit S)

def QMALocalOn (S : Finset ι) (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) : Prop :=
  ∃ B : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ, A = qmaLocalLift S B

theorem qmaLocalLift_add (S : Finset ι) (A B : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) :
    qmaLocalLift S (A+B) = qmaLocalLift S A+qmaLocalLift S B := by
  simp [qmaLocalLift,Matrix.add_kronecker,Matrix.submatrix_add]

theorem qmaLocalLift_smul (S : Finset ι) (a : ℂ)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) :
    qmaLocalLift S (a • A) = a • qmaLocalLift S A := by
  simp [qmaLocalLift,Matrix.smul_kronecker,Matrix.submatrix_smul]

theorem qmaLocalLift_mul (S : Finset ι) (A B : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) :
    qmaLocalLift S (A*B) = qmaLocalLift S A*qmaLocalLift S B := by
  unfold qmaLocalLift
  rw [Matrix.submatrix_mul_equiv,←Matrix.mul_kronecker_mul,one_mul]

theorem qmaLocalLift_adjoint (S : Finset ι) (A : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) :
    qmaLocalLift S A.conjTranspose = (qmaLocalLift S A).conjTranspose := by
  simp [qmaLocalLift,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_submatrix]

theorem qmaLocalLift_one (S : Finset ι) : qmaLocalLift S 1 = 1 := by
  unfold qmaLocalLift
  rw [Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]

theorem QMALocalOn.add {S : Finset ι} {A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) (hB : QMALocalOn S B) : QMALocalOn S (A+B) := by
  obtain ⟨a,rfl⟩ := hA
  obtain ⟨b,rfl⟩ := hB
  exact ⟨a+b,(qmaLocalLift_add S a b).symm⟩

theorem QMALocalOn.mul {S : Finset ι} {A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) (hB : QMALocalOn S B) : QMALocalOn S (A*B) := by
  obtain ⟨a,rfl⟩ := hA
  obtain ⟨b,rfl⟩ := hB
  exact ⟨a*b,(qmaLocalLift_mul S a b).symm⟩

theorem QMALocalOn.smul {S : Finset ι} {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) (z : ℂ) : QMALocalOn S (z • A) := by
  obtain ⟨a,rfl⟩ := hA
  exact ⟨z • a,(qmaLocalLift_smul S z a).symm⟩

theorem QMALocalOn.adjoint {S : Finset ι} {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) : QMALocalOn S A.conjTranspose := by
  obtain ⟨a,rfl⟩ := hA
  exact ⟨a.conjTranspose,(qmaLocalLift_adjoint S a).symm⟩

end ContinuumCoulomb

end

end OAI
