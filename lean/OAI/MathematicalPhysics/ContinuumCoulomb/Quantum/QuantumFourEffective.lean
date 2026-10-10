import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourCouplingScale

namespace OAI

/-! The actual inter-block coupling has the desired second-order X/Z term. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

def qmaFourCoupling (a b : Fin 2) (j : ℝ) : Matrix (Fin 16 × Fin 16) (Fin 16 × Fin 16) ℂ :=
  (qmaFourCouplingSize a b j:ℂ) • qmaFourWeightedCross
    (qmaFourAxisWeights a true) (qmaFourAxisWeights b (qmaFourCouplingSign j))

def qmaFourCouplingFactor (a b : Fin 2) (j : ℝ) : ℝ := (3/8)*(qmaFourCouplingSize a b j)^2

def qmaFourCouplingEffective (a b : Fin 2) (j : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (-1/8:ℂ) • ((qmaFourCoupling a b j*qmaFourDoubleEncoding).conjTranspose*
    (qmaFourCoupling a b j*qmaFourDoubleEncoding))

theorem qmaFourCouplingEffective_tensor (a b : Fin 2) (j : ℝ) :
    qmaFourCouplingEffective a b j = (-qmaFourCouplingFactor a b j:ℂ) •
      (((qmaFourAxisShift a true:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+
        (qmaFourAxisScale a:ℂ) • qmaFourAxis a) ⊗ₖ
      ((qmaFourAxisShift b (qmaFourCouplingSign j):ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+
        ((qmaFourAxisSign (qmaFourCouplingSign j)*qmaFourAxisScale b:ℝ):ℂ) • qmaFourAxis b)) := by
  rw [qmaFourCouplingEffective,qmaFourCoupling,Matrix.smul_mul,Matrix.conjTranspose_smul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,smul_smul]
  rw [qmaFourWeightedCross_gram,qmaFourAxisWeights_correlation,qmaFourAxisWeights_correlation]
  simp only [qmaFourAxisSign,ite_true,one_mul,Complex.star_def,Complex.conj_ofReal,
    smul_smul,qmaFourCouplingFactor]
  push_cast
  congr 1
  ring

theorem qmaFourCouplingEffective_expansion (a b : Fin 2) (j : ℝ) :
    qmaFourCouplingEffective a b j =
      (-qmaFourCouplingFactor a b j*qmaFourAxisShift a true*
        qmaFourAxisShift b (qmaFourCouplingSign j):ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)+
      (-qmaFourCouplingFactor a b j*qmaFourAxisScale a*
        qmaFourAxisShift b (qmaFourCouplingSign j):ℂ) •
          (qmaFourAxis a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))+
      (-qmaFourCouplingFactor a b j*qmaFourAxisShift a true*
        (qmaFourAxisSign (qmaFourCouplingSign j)*qmaFourAxisScale b):ℂ) •
          ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ qmaFourAxis b)+
      (j:ℂ) • (qmaFourAxis a ⊗ₖ qmaFourAxis b) := by
  have hc : (-qmaFourCouplingFactor a b j*qmaFourAxisScale a*
      (qmaFourAxisSign (qmaFourCouplingSign j)*qmaFourAxisScale b):ℂ) = j := by
    have h := qmaFourCouplingSign_calibration a b j
    have he : -qmaFourCouplingFactor a b j*qmaFourAxisScale a*
        (qmaFourAxisSign (qmaFourCouplingSign j)*qmaFourAxisScale b) = j := by
      unfold qmaFourCouplingFactor
      nlinarith [h]
    exact_mod_cast he
  rw [← hc,qmaFourCouplingEffective_tensor]
  simp only [Matrix.add_kronecker,Matrix.kronecker_add,Matrix.smul_kronecker,
    Matrix.kronecker_smul,Matrix.one_kronecker_one,smul_add,smul_smul]
  push_cast
  module

end ContinuumCoulomb

end

end OAI
