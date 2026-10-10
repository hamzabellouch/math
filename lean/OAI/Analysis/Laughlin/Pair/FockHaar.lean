import OAI.Analysis.Laughlin.Fock.EnergyRotation
import OAI.Analysis.Laughlin.Fock.HaarQuadratic
import OAI.Analysis.Laughlin.Spin.Schur

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem contractionForm_smul {I : Type*} [Fintype I] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (c : ℂ) (M : Matrix I I ℂ) (x : Space Q) :
    contractionForm Q minus (c • M) x = c * contractionForm Q minus M x := by
  simp only [contractionForm,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

theorem contractionForm_sum {I J : Type*} [Fintype I] [Fintype J] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (M : J → Matrix I I ℂ) (x : Space Q) :
    contractionForm Q minus (∑ j, M j) x = ∑ j, contractionForm Q minus (M j) x := by
  simp only [contractionForm,Matrix.sum_apply,Finset.sum_mul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem pair_contractionForm_one (Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val) 1 x =
      (sourceFockEnergy Q x : ℂ) := by
  rw [sourceFockEnergy_eq_fin Q hQ]
  simp [contractionForm,Matrix.one_apply,occupationInner_self,Complex.ofReal_sum]

theorem physical_pairFock_haar (Q : ℕ) (hQ : 0 < Q)
    (M : Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ) (x : Space Q) :
    (∫ g, contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val) M
      (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
      (Matrix.trace M/(2*Q-2+1 : ℕ)) * (sourceFockEnergy Q x : ℂ) := by
  rw [contractionForm_haar Q (sourceSpinRepresentation (2*Q-2))
    (sourceSpinRepresentation_inv (2*Q-2)) (sourceSpinRepresentation_continuous (2*Q-2))
    _ (sourcePairEnd_rotation Q hQ),source_spin_haar_schur,contractionForm_smul,
    pair_contractionForm_one Q hQ]

theorem physical_pair_norm_haar (Q : ℕ) (hQ : 0 < Q) (p : Fin (2*Q-2+1)) (x : Space Q) :
    (∫ g, (occupationNormSq Q (sourcePairEnd Q p.val (exteriorRotation Q g⁻¹ x)) : ℂ)
      ∂sourceHaar) = (sourceFockEnergy Q x : ℂ)/(2*Q-2+1 : ℕ) := by
  let M : Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ :=
    fun i j => if i=p ∧ j=p then 1 else 0
  have hm (y : Space Q) : contractionForm Q
      (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val) M y =
      (occupationNormSq Q (sourcePairEnd Q p.val y) : ℂ) := by
    simp [contractionForm,M,occupationInner_self,ite_and]
  have ht : Matrix.trace M=1 := by simp [Matrix.trace,Matrix.diag,M]
  have h := physical_pairFock_haar Q hQ M x
  simpa only [hm,ht,one_div,mul_comm,div_eq_mul_inv,one_mul] using h

end Laughlin.Fock

end OAI
