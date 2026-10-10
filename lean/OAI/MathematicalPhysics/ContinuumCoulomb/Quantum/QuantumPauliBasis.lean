import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRealLocalFamily

namespace OAI

/-! Exact Pauli expansion on the bounded supports of the circuit terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaPauli (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ := ![1,pauliX,pauliY,pauliZ] i

theorem qmaPauli_hermitian (i : Fin 4) : (qmaPauli i).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaPauli,pauli,pauliX,pauliY,pauliZ]

theorem qmaPauli_kernel (a b c d : Fin 2) :
    (∑ i : Fin 4, qmaPauli i a b*qmaPauli i c d) =
      2*(if a = d ∧ c = b then (1:ℂ) else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [qmaPauli,pauli,pauliX,pauliY,pauliZ,Fin.sum_univ_succ]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaPauliWord (w : ι → Fin 4) : Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  fun s t => ∏ i, qmaPauli (w i) (s i) (t i)

omit [DecidableEq ι] in
theorem qmaPauliWord_hermitian (w : ι → Fin 4) : (qmaPauliWord w).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro s t
  change star (∏ i, qmaPauli (w i) (t i) (s i)) = ∏ i, qmaPauli (w i) (s i) (t i)
  rw [star_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (qmaPauli_hermitian (w i)).apply _ _

theorem qmaPauliWord_kernel (s t u v : ι → Fin 2) :
    (∑ w : ι → Fin 4, qmaPauliWord w s t*qmaPauliWord w u v) =
      (2:ℂ)^Fintype.card ι*(if s = v ∧ u = t then 1 else 0) := by
  simp only [qmaPauliWord,←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun (i : ι) (a : Fin 4) =>
    qmaPauli a (s i) (t i)*qmaPauli a (u i) (v i))]
  simp only [qmaPauli_kernel,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  congr 1
  by_cases hs : s = v
  · subst v
    by_cases hu : u = t
    · subst u
      simp
    · rw [ite_eq_right (by simp [hu])]
      obtain ⟨i,hi⟩ := Function.ne_iff.mp hu
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  · rw [ite_eq_right (by simp [hs])]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hs
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end ContinuumCoulomb

end

end OAI
