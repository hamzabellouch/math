import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorWeighted
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorCompression

namespace OAI

/-! Physical counterterms calibrate each edge of the full tensor simulator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

def qmaFourTensorCoupling (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  (qmaFourCouplingSize a b t:ℂ) • qmaFourTensorWeighted i j
    (qmaFourAxisWeights a true) (qmaFourAxisWeights b (qmaFourCouplingSign t))

def qmaFourTensorEffective (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  (-1/8:ℂ) • ((qmaFourTensorCoupling i j a b t*qmaFourTensorEncoding n).conjTranspose*
    (qmaFourTensorCoupling i j a b t*qmaFourTensorEncoding n))

theorem qmaFourTensorEffective_tensor (i j : Fin n) (hij : i ≠ j) (a b : Fin 2) (t : ℝ) :
    qmaFourTensorEffective i j a b t = (-qmaFourCouplingFactor a b t:ℂ) •
      qmaPairMatrix i j
        ((qmaFourAxisShift a true:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+
          (qmaFourAxisScale a:ℂ) • qmaFourAxis a)
        ((qmaFourAxisShift b (qmaFourCouplingSign t):ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+
          ((qmaFourAxisSign (qmaFourCouplingSign t)*qmaFourAxisScale b:ℝ):ℂ) • qmaFourAxis b) := by
  rw [qmaFourTensorEffective,qmaFourTensorCoupling,Matrix.smul_mul,Matrix.conjTranspose_smul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,smul_smul]
  rw [qmaFourTensorWeighted_gram i j hij,qmaFourAxisWeights_correlation,qmaFourAxisWeights_correlation]
  simp only [qmaFourAxisSign,ite_true,one_mul,Complex.star_def,Complex.conj_ofReal,
    smul_smul,qmaFourCouplingFactor]
  push_cast
  congr 1
  ring

theorem qmaFourTensorEffective_expansion (i j : Fin n) (hij : i ≠ j) (a b : Fin 2) (t : ℝ) :
    qmaFourTensorEffective i j a b t =
      (-qmaFourCouplingFactor a b t*qmaFourAxisShift a true*
        qmaFourAxisShift b (qmaFourCouplingSign t):ℂ) • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)+
      (-qmaFourCouplingFactor a b t*qmaFourAxisScale a*
        qmaFourAxisShift b (qmaFourCouplingSign t):ℂ) • qmaSiteMatrix i (qmaFourAxis a)+
      (-qmaFourCouplingFactor a b t*qmaFourAxisShift a true*
        (qmaFourAxisSign (qmaFourCouplingSign t)*qmaFourAxisScale b):ℂ) • qmaSiteMatrix j (qmaFourAxis b)+
      (t:ℂ) • qmaPairMatrix i j (qmaFourAxis a) (qmaFourAxis b) := by
  have hc : (-qmaFourCouplingFactor a b t*qmaFourAxisScale a*
      (qmaFourAxisSign (qmaFourCouplingSign t)*qmaFourAxisScale b):ℂ) = t := by
    have h := qmaFourCouplingSign_calibration a b t
    have he : -qmaFourCouplingFactor a b t*qmaFourAxisScale a*
        (qmaFourAxisSign (qmaFourCouplingSign t)*qmaFourAxisScale b) = t := by
      unfold qmaFourCouplingFactor
      nlinarith [h]
    exact_mod_cast he
  rw [← hc,qmaFourTensorEffective_tensor i j hij]
  simp only [qmaPairMatrix_add_left _ _ hij,qmaPairMatrix_add_right _ _ hij,
    qmaPairMatrix_smul_left _ _ hij,qmaPairMatrix_smul_right _ _ hij,
    qmaPairMatrix_one_right _ _ hij,qmaPairMatrix_one_left _ _ hij,qmaSiteMatrix_one,
    smul_add,smul_smul]
  push_cast
  module

def qmaFourTensorCounterterm (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  qmaSiteMatrix i (qmaFourAxisField a (qmaFourCounterA a b t))+
    qmaSiteMatrix j (qmaFourAxisField b (qmaFourCounterB a b t))

theorem qmaFourTensorCounterterm_effective (i j : Fin n) (hij : i ≠ j) (a b : Fin 2) (t : ℝ) :
    (qmaFourTensorEncoding n).conjTranspose*qmaFourTensorCounterterm i j a b t*qmaFourTensorEncoding n+
      qmaFourTensorEffective i j a b t =
      (t:ℂ) • qmaPairMatrix i j (qmaFourAxis a) (qmaFourAxis b)+
      (qmaFourEnergyOffset a b t:ℂ) • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) := by
  rw [qmaFourTensorCounterterm,Matrix.mul_add,Matrix.add_mul,
    qmaFourTensor_site_compression,qmaFourTensor_site_compression,
    qmaFourAxisField_compression,qmaFourAxisField_compression,qmaFourTensorEffective_expansion i j hij]
  simp only [qmaSiteMatrix_add,qmaSiteMatrix_smul,qmaSiteMatrix_one,
    qmaFourEnergyOffset,qmaFourCounterA,qmaFourCounterB]
  push_cast
  module

end ContinuumCoulomb

end

end OAI
