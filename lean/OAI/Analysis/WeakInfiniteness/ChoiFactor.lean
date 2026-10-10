import Mathlib
import OAI.Analysis.WeakInfiniteness.MatrixTensorExact

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra ComplexOrder

universe u

section MatrixUnits

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
lemma matrixUnit_star (i j : n) : star (matrixUnit i j)=matrixUnit j i := by
  ext k l
  change star (if l=i ∧ k=j then (1:ℂ) else 0)=(if k=j ∧ l=i then 1 else 0)
  by_cases h : l=i ∧ k=j
  · simp [h]
  · have hh : ¬(k=j ∧ l=i) := by tauto
    simp [h,hh]

lemma matrixUnit_mul (i j k l : n) :
    matrixUnit i j*matrixUnit k l=if j=k then matrixUnit i l else 0 := by
  ext a b
  change (∑ c,(if a=i ∧ c=j then (1:ℂ) else 0)*(if c=k ∧ b=l then 1 else 0))=_
  by_cases h : j=k
  · subst k
    rw [ite_eq_left rfl]
    change _=if a=i ∧ b=l then (1:ℂ) else 0
    by_cases ha : a=i <;> by_cases hb : b=l <;> simp [ha,hb]
  · simp only [ite_eq_right h]
    change _=0
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : c=j
    · subst c; simp [h]
    · simp [hc]

lemma matrixUnits_nonneg (k : n) :
    0≤(CStarMatrix.ofMatrix (fun i j : n => matrixUnit i j) :
      CStarMatrix n n (CStarMatrix n n ℂ)) := by
  let R : CStarMatrix n n (CStarMatrix n n ℂ) :=
    CStarMatrix.ofMatrix (fun i j => if i=k then matrixUnit k j else 0)
  have he : star R*R=CStarMatrix.ofMatrix (fun i j : n => matrixUnit i j) := by
    ext i j a b
    have hentry : (star R*R) i j=matrixUnit i j := by
      change (∑ l,star (if l=k then matrixUnit k i else 0)*(if l=k then matrixUnit k j else 0))=_
      rw [Finset.sum_eq_single k]
      · simp [matrixUnit_star,matrixUnit_mul]
      · intro l _ hl
        simp [hl]
      · simp
    exact congrArg (fun M : CStarMatrix n n ℂ => M a b) hentry
  rw [← he]
  exact star_mul_self_nonneg R

end MatrixUnits

section Coefficients

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance choiMatrixRealModule {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n A) := Module.complexToReal _

lemma completelyPositive_matrix_gram {n : ℕ} (hn : 1≤n)
    (ψ : CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] A) (hψ : CompletelyPositive ψ) :
    ∃ X : CStarMatrix (Fin n) (Fin n) A,∀ i j,
      ψ (matrixUnit i j)=∑ k,star (X k i)*X k j := by
  let M : CStarMatrix (Fin n) (Fin n) A :=
    matrixLinearMap ψ (CStarMatrix.ofMatrix (fun i j : Fin n => matrixUnit i j))
  have hM : 0≤M := matrixLinearMap_nonneg hψ (matrixUnits_nonneg (⟨0,by omega⟩ : Fin n))
  let X := CFC.sqrt M
  have hX : star X*X=M := by
    rw [show star X=X from (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg M)).star_eq]
    exact CFC.sqrt_mul_sqrt_self M hM
  refine ⟨X,?_⟩
  intro i j
  have he := congrArg (fun Z : CStarMatrix (Fin n) (Fin n) A => Z i j) hX
  exact he.symm

omit [PartialOrder A] [StarOrderedRing A] in
lemma completelyPositive_matrix_expansion {n : ℕ}
    (ψ : CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] A)
    (X : CStarMatrix (Fin n) (Fin n) A)
    (hX : ∀ i j,ψ (matrixUnit i j)=∑ k,star (X k i)*X k j)
    (M : CStarMatrix (Fin n) (Fin n) ℂ) :
    ψ M=∑ i,∑ j,M i j • (∑ k,star (X k i)*X k j) := by
  conv_lhs => rw [← matrix_unit_expansion M]
  simp only [map_sum,map_smul,hX]

end Coefficients

end

end WeakPureInfiniteness
end

end OAI
