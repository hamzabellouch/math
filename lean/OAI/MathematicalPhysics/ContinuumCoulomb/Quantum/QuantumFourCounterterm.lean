import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourEffective

namespace OAI

/-! Internal exchanges cancel the unwanted one-body terms of the simulator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

def qmaFourCounterA (a b : Fin 2) (j : ℝ) : ℝ :=
  qmaFourCouplingFactor a b j*qmaFourAxisScale a*qmaFourAxisShift b (qmaFourCouplingSign j)

def qmaFourCounterB (a b : Fin 2) (j : ℝ) : ℝ :=
  qmaFourCouplingFactor a b j*qmaFourAxisShift a true*
    (qmaFourAxisSign (qmaFourCouplingSign j)*qmaFourAxisScale b)

def qmaFourCounterterm (a b : Fin 2) (j : ℝ) : Matrix (Fin 16 × Fin 16) (Fin 16 × Fin 16) ℂ :=
  qmaFourAxisField a (qmaFourCounterA a b j) ⊗ₖ (1 : Matrix (Fin 16) (Fin 16) ℂ)+
    (1 : Matrix (Fin 16) (Fin 16) ℂ) ⊗ₖ qmaFourAxisField b (qmaFourCounterB a b j)

def qmaFourEnergyOffset (a b : Fin 2) (j : ℝ) : ℝ :=
  qmaFourAxisFieldShift a (qmaFourCounterA a b j)+
    qmaFourAxisFieldShift b (qmaFourCounterB a b j)-
    qmaFourCouplingFactor a b j*qmaFourAxisShift a true*qmaFourAxisShift b (qmaFourCouplingSign j)

theorem qmaFourDouble_local_compression (A B : Matrix (Fin 16) (Fin 16) ℂ) :
    qmaFourDoubleEncoding.conjTranspose*
      (A ⊗ₖ (1 : Matrix (Fin 16) (Fin 16) ℂ)+(1 : Matrix (Fin 16) (Fin 16) ℂ) ⊗ₖ B)*
      qmaFourDoubleEncoding =
      (qmaFourEncoding.conjTranspose*A*qmaFourEncoding) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)+
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (qmaFourEncoding.conjTranspose*B*qmaFourEncoding) := by
  simp only [qmaFourDoubleEncoding,Matrix.conjTranspose_kronecker,Matrix.mul_add,Matrix.add_mul,
    ← Matrix.mul_kronecker_mul,Matrix.mul_one,qmaFourEncoding_gram]

theorem qmaFourCounterterm_effective (a b : Fin 2) (j : ℝ) :
    qmaFourDoubleEncoding.conjTranspose*qmaFourCounterterm a b j*qmaFourDoubleEncoding+
      qmaFourCouplingEffective a b j =
      (j:ℂ) • (qmaFourAxis a ⊗ₖ qmaFourAxis b)+
      (qmaFourEnergyOffset a b j:ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  rw [qmaFourCounterterm,qmaFourDouble_local_compression,qmaFourAxisField_compression,
    qmaFourAxisField_compression,qmaFourCouplingEffective_expansion]
  simp only [Matrix.add_kronecker,Matrix.kronecker_add,Matrix.smul_kronecker,
    Matrix.kronecker_smul,Matrix.one_kronecker_one,qmaFourEnergyOffset,qmaFourCounterA,qmaFourCounterB]
  push_cast
  module

end ContinuumCoulomb

end

end OAI
