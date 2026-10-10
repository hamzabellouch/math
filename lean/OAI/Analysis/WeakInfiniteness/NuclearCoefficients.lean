import Mathlib
import OAI.Analysis.WeakInfiniteness.ChoiFactor
import OAI.Analysis.WeakInfiniteness.NuclearExact
import OAI.Analysis.WeakInfiniteness.UnitalCuntzEmbedding

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

section Folding

variable {A : Type u} [CStarAlgebra A]

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma matrixUnits_sum_diagonal : (∑ i : n,matrixUnit i i)=(1:CStarMatrix n n ℂ) := by
  ext a b
  change matrixEntryLinear a b (∑ i : n,matrixUnit i i)=(1:CStarMatrix n n ℂ) a b
  simp only [map_sum]
  change (∑ i,if a=i ∧ b=i then (1:ℂ) else 0)=if a=b then 1 else 0
  by_cases h : a=b
  · subst b
    simp
  · apply Eq.trans (Finset.sum_eq_zero ?_) (by simp [h])
    intro i _
    have hh : ¬(a=i ∧ b=i) := by rintro ⟨rfl,rfl⟩; exact h rfl
    simp [hh]

lemma fold_matrix_gram (r : n → A) (hr : ∀ i j,star (r i)*r j=if i=j then 1 else 0)
    (X : CStarMatrix n n A) (i j : n) :
    star (∑ k,r k*X k i)*(∑ k,r k*X k j)=∑ k,star (X k i)*X k j := by
  have he (k l : n) : star (r k*X k i)*(r l*X l j)=
      if k=l then star (X k i)*X k j else 0 := by
    calc
      _ = star (X k i)*(star (r k)*r l)*X l j := by simp only [star_mul,mul_assoc]
      _ = _ := by
        rw [hr]
        split_ifs with h
        · subst l; simp
        · simp
  calc
    _ = ∑ k,∑ l,star (r k*X k i)*(r l*X l j) := by
      rw [star_sum,Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = _ := by simp only [he,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

end Folding

section Realization

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma completelyPositive_realize_coefficients {n : ℕ} (hn : 1≤n)
    (r : Fin n → A) (hr : ∀ i j,star (r i)*r j=if i=j then 1 else 0)
    (ψ : CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] A) (hψ : CompletelyPositive ψ) :
    ∃ v : Fin n → A,(∀ i j,ψ (matrixUnit i j)=star (v i)*v j) ∧
      (∀ M,ψ M=∑ i,∑ j,M i j • (star (v i)*v j)) ∧
      (∑ i,star (v i)*v i)=ψ 1 := by
  obtain ⟨X,hX⟩ := completelyPositive_matrix_gram hn ψ hψ
  let v : Fin n → A := fun i => ∑ k,r k*X k i
  have hv (i j : Fin n) : ψ (matrixUnit i j)=star (v i)*v j := by
    rw [hX,fold_matrix_gram r hr X]
  refine ⟨v,hv,?_,?_⟩
  · intro M
    conv_lhs => rw [← matrix_unit_expansion M]
    simp only [map_sum,map_smul,hv]
  · simp only [← hv,← map_sum,matrixUnits_sum_diagonal]

lemma nuclear_weaklyPurelyInfinite_coefficient_approximation
    (hN : Nuclear A) (hW : WeaklyPurelyInfinite A)
    (F : Finset A) (ε : ℝ) (hε : 0<ε) :
    ∃ n : ℕ,1≤n ∧∃ φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ,
      ∃ v : Fin n → A,CompletelyPositive φ ∧ ‖φ‖≤1 ∧
      ‖∑ i,star (v i)*v i‖≤1 ∧
      ∀ a∈F,‖(∑ i,∑ j,φ a i j • (star (v i)*v j))-a‖<ε := by
  obtain ⟨r,s,hr,hs,hrs⟩ := exists_two_isometries_of_properlyInfinite
    (exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any (nuclear_exact hN) hW zero_le_one)
  obtain ⟨n,hn,φ,ψ,hφ,hψ,hφn,hψn,happ⟩ := hN F ε hε
  let R : Fin n → A := fun k => s^(k:ℕ)*r
  have hR (i j : Fin n) : star (R i)*R j=if i=j then 1 else 0 := by
    have hh := binaryCuntzFamily_relations hr hs hrs (i:ℕ) (j:ℕ)
    simpa only [Fin.val_inj] using hh
  obtain ⟨v,_,hv,hv1⟩ := completelyPositive_realize_coefficients hn R hR ψ hψ
  refine ⟨n,hn,φ,v,hφ,hφn,?_,?_⟩
  · rw [hv1]
    let : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
    calc
      _ ≤ ‖ψ‖*‖(1:CStarMatrix (Fin n) (Fin n) ℂ)‖ := ψ.le_opNorm 1
      _ ≤ 1 := by rw [norm_one,mul_one]; exact hψn
  · intro a ha
    rw [← hv]
    exact happ a ha

end Realization

end

end WeakPureInfiniteness
end

end OAI
