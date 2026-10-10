import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliAlgebra

namespace OAI

/-! Exact Pauli multiplication, including the scalar phases needed to
replace a YY interaction by commuting real X/Z factors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaPauliProductIndex (a b : Fin 4) : Fin 4 :=
  ![![0,1,2,3],![1,0,3,2],![2,3,0,1],![3,2,1,0]] a b

def qmaPauliProductPhase (a b : Fin 4) : ℂ :=
  ![![1,1,1,1],![1,1,Complex.I,-Complex.I],
    ![1,-Complex.I,1,Complex.I],![1,Complex.I,-Complex.I,1]] a b

theorem qmaPauli_product (a b : Fin 4) :
    qmaPauli a*qmaPauli b = qmaPauliProductPhase a b • qmaPauli (qmaPauliProductIndex a b) := by
  fin_cases a <;> fin_cases b <;> ext s t <;> fin_cases s <;> fin_cases t <;>
    norm_num [qmaPauliProductIndex,qmaPauliProductPhase,qmaPauli,pauliX,pauliY,pauliZ,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaPauliWord_product (a b : ι → Fin 4) :
    qmaPauliWord a*qmaPauliWord b = (∏ i, qmaPauliProductPhase (a i) (b i)) •
      qmaPauliWord (fun i => qmaPauliProductIndex (a i) (b i)) := by
  ext s t
  rw [qmaPauliWord_mul_apply]
  simp only [qmaPauli_product,Matrix.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,qmaPauliWord]

end ContinuumCoulomb

end

end OAI
