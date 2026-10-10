import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCircuitPauli

namespace OAI

/-! The Pauli factors used by the mediator gadgets are Hermitian
involutions, and disjoint factors commute exactly. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaPauli_zero : qmaPauli 0 = 1 := rfl

theorem qmaPauli_square (i : Fin 4) : qmaPauli i*qmaPauli i = 1 := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaPauli,pauliX,pauliY,pauliZ,Matrix.mul_apply,Fin.sum_univ_two]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaPauliWord_mul_apply (w v : ι → Fin 4) (s t : ι → Fin 2) :
    (qmaPauliWord w*qmaPauliWord v) s t =
      ∏ i, (qmaPauli (w i)*qmaPauli (v i)) (s i) (t i) := by
  change (∑ r : ι → Fin 2, (∏ i, qmaPauli (w i) (s i) (r i))*(∏ i, qmaPauli (v i) (r i) (t i))) = _
  simp only [←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => qmaPauli (w i) (s i) a*qmaPauli (v i) a (t i))).symm

theorem qmaPauliWord_square (w : ι → Fin 4) : qmaPauliWord w*qmaPauliWord w = 1 := by
  ext s t
  rw [qmaPauliWord_mul_apply]
  simp only [qmaPauli_square,Matrix.one_apply]
  by_cases h : s = t
  · subst t
    simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem qmaPauliWord_gram (w : ι → Fin 4) :
    (qmaPauliWord w).conjTranspose*qmaPauliWord w = 1 := by
  rw [qmaPauliWord_hermitian w,qmaPauliWord_square]

theorem qmaPauliWord_disjoint_commute (w v : ι → Fin 4)
    (h : ∀ i, w i = 0 ∨ v i = 0) : qmaPauliWord w*qmaPauliWord v = qmaPauliWord v*qmaPauliWord w := by
  ext s t
  rw [qmaPauliWord_mul_apply,qmaPauliWord_mul_apply]
  apply Finset.prod_congr rfl
  intro i _
  rcases h i with hi | hi <;> simp [hi,qmaPauli_zero]

end ContinuumCoulomb

end

end OAI
