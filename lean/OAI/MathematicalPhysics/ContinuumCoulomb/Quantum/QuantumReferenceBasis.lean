import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridLocality
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRealification

namespace OAI

/-! A local Y-eigenbasis for distributing the realification reference qubit. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Kronecker Classical

def qmaReferencePhase : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,Complex.I]

def qmaReferenceBasis : Matrix (Fin 2) (Fin 2) ℂ := qmaReferencePhase*qmaHadamard

def qmaImaginaryRotation : Matrix (Fin 2) (Fin 2) ℂ := !![0,-1;1,0]

theorem qmaReferencePhase_gram : qmaReferencePhase.conjTranspose*qmaReferencePhase = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qmaReferencePhase,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two]

theorem qmaReferenceBasis_gram : qmaReferenceBasis.conjTranspose*qmaReferenceBasis = 1 := by
  simp only [qmaReferenceBasis,Matrix.conjTranspose_mul,mul_assoc]
  rw [←mul_assoc qmaReferencePhase.conjTranspose,qmaReferencePhase_gram,one_mul,qmaHadamard_gram]

theorem qmaReferenceBasis_y :
    qmaReferenceBasis.conjTranspose*pauliY*qmaReferenceBasis = pauliZ := by
  have hphase : qmaReferencePhase.conjTranspose*pauliY*qmaReferencePhase = pauliX := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [qmaReferencePhase,pauliY,pauliX,Matrix.mul_apply,
        Matrix.conjTranspose_apply,Fin.sum_univ_two]
  have hhad : qmaHadamard.conjTranspose*pauliX*qmaHadamard = pauliZ := by
    have hraw : (!![1,1;1,-1] : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose*
        pauliX*!![1,1;1,-1] = (2:ℂ) • pauliZ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [pauliX,pauliZ,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two]
    unfold qmaHadamard
    rw [Matrix.conjTranspose_smul,bellScale_star,smul_mul_assoc,smul_mul_assoc,
      mul_smul_comm,hraw,smul_smul,smul_smul]
    rw [show bellScale*bellScale*2 = (1:ℂ) by rw [←pow_two,bellScale_sq]; norm_num]
    exact one_smul _ _
  calc
    _ = qmaHadamard.conjTranspose*
        (qmaReferencePhase.conjTranspose*pauliY*qmaReferencePhase)*qmaHadamard := by
      simp only [qmaReferenceBasis,Matrix.conjTranspose_mul,mul_assoc]
    _ = _ := by rw [hphase,hhad]

theorem qmaImaginaryRotation_eq : qmaImaginaryRotation = (-Complex.I) • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [qmaImaginaryRotation,pauliY]

theorem qmaReferenceBasis_rotation :
    qmaReferenceBasis.conjTranspose*qmaImaginaryRotation*qmaReferenceBasis =
      (-Complex.I) • pauliZ := by
  rw [qmaImaginaryRotation_eq,mul_smul_comm,smul_mul_assoc,qmaReferenceBasis_y]

def qmaEntryReal {ι : Type*} (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => (A i j).re

def qmaEntryImag {ι : Type*} (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => (A i j).im

theorem qmaRebitMatrix_tensor {ι : Type*} (A : Matrix ι ι ℂ) :
    qmaRebitMatrix A =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ qmaEntryReal A +
        qmaImaginaryRotation ⊗ₖ qmaEntryImag A := by
  ext ⟨b,i⟩ ⟨c,j⟩
  fin_cases b <;> fin_cases c <;>
    simp [qmaRebitMatrix,qmaEntryReal,qmaEntryImag,qmaImaginaryRotation]

end ContinuumCoulomb

end

end OAI
