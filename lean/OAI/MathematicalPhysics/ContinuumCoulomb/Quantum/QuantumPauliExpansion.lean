import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliBasis

namespace OAI

/-! Coefficients of the actual small local matrices in the Pauli basis. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaPauliCoefficient (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (w : ι → Fin 4) : ℂ :=
  ((2:ℂ)^Fintype.card ι)⁻¹ * ∑ s, ∑ t, A s t*qmaPauliWord w t s

theorem qmaPauli_expansion (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    (∑ w : ι → Fin 4, qmaPauliCoefficient A w • qmaPauliWord w) = A := by
  ext i j
  have hswap :
      (∑ w : ι → Fin 4, ∑ s : ι → Fin 2, ∑ t : ι → Fin 2,
        A s t*(qmaPauliWord w i j*qmaPauliWord w t s)) =
      ∑ s : ι → Fin 2, ∑ t : ι → Fin 2, ∑ w : ι → Fin 4,
        A s t*(qmaPauliWord w i j*qmaPauliWord w t s) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_comm]
  calc
    _ = ((2:ℂ)^Fintype.card ι)⁻¹ *
        ∑ w : ι → Fin 4, ∑ s : ι → Fin 2, ∑ t : ι → Fin 2,
          A s t*(qmaPauliWord w i j*qmaPauliWord w t s) := by
      simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,qmaPauliCoefficient,
        Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = ((2:ℂ)^Fintype.card ι)⁻¹ *
        ∑ s : ι → Fin 2, ∑ t : ι → Fin 2,
          A s t*(∑ w : ι → Fin 4, qmaPauliWord w i j*qmaPauliWord w t s) := by
      rw [hswap]
      simp only [Finset.mul_sum]
    _ = A i j := by
      simp_rw [qmaPauliWord_kernel]
      simp only [mul_ite,ite_and,mul_one,mul_zero,Finset.sum_ite_irrel,
        Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
      have hp : (2:ℂ)^Fintype.card ι ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
      simp

end ContinuumCoulomb

end

end OAI
