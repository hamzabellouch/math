import Mathlib.Tactic.FinCases
import OAI.Geometry.NodalSets.Coefficients.RealFintypeCoefficientBound
import OAI.Geometry.NodalSets.Elliptic.RealWeakSecondCommutator

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_second_commutator_bound {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (C : Coord n → Fin n → Fin n → ℝ)
    (hC : ∀ a j, ContDiff ℝ ∞ (fun x ↦ C x a j)) (k l j : Fin n) :
    ∃ D > 0, ∀ (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ),
      (∀ a, MemLp (U a) 2 (volume.restrict K)) →
      (∀ a b, MemLp (H a b) 2 (volume.restrict K)) →
      ∀ E : ℝ, 0 ≤ E → (∀ a, (∫ x in K, (U a x)^2) ≤ E) →
      (∀ a b, (∫ x in K, (H a b x)^2) ≤ E) →
        MemLp (realSecondCommutator C U H k l j) 2 (volume.restrict K) ∧
        (∫ x in K, (realSecondCommutator C U H k l j x)^2) ≤ D*E := by
  let A : Coord n → (Fin n × Fin 3) → ℝ := fun x t ↦
    let a := t.1
    ![coordPartial (fun y ↦ C y a j) x l,coordPartial (fun y ↦ C y a j) x k,coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x l] t.2
  have hA (t : Fin n × Fin 3) : Continuous (fun x ↦ A x t) := by
    rcases t with ⟨a,b⟩
    fin_cases b
    · exact (real_coordPartial_smooth _ (hC a j) l).continuous
    · exact (real_coordPartial_smooth _ (hC a j) k).continuous
    · exact (real_coordPartial_smooth _ (real_coordPartial_smooth _ (hC a j) k) l).continuous
  obtain ⟨D,hD,hb⟩ := real_compact_fintype_coefficient_common_bound hK A hA
  refine ⟨D,hD,fun U H hU hH E hE hUE hHE ↦ ?_⟩
  let V : (Fin n × Fin 3) → Coord n → ℝ := fun t ↦
    let a := t.1
    ![H a k,H a l,U a] t.2
  have hV (t : Fin n × Fin 3) : MemLp (V t) 2 (volume.restrict K) := by
    rcases t with ⟨a,b⟩
    fin_cases b
    · exact hH a k
    · exact hH a l
    · exact hU a
  have hVE (t : Fin n × Fin 3) : (∫ x in K, (V t x)^2) ≤ E := by
    rcases t with ⟨a,b⟩
    fin_cases b
    · exact hHE a k
    · exact hHE a l
    · exact hUE a
  have h := hb V hV E hE hVE
  have heq : (fun x ↦ ∑ t, A x t*V t x)=realSecondCommutator C U H k l j := by
    funext x
    simp [A,V,realSecondCommutator,Fintype.sum_prod_type,Fin.sum_univ_succ,add_assoc]
  rw [heq] at h
  simp_rw [show ∀ x, _ = _ from fun x ↦ congrFun heq x] at h
  exact h

theorem real_second_commutator_derivative_bound {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (C : Coord n → Fin n → Fin n → ℝ)
    (hC : ∀ a j, ContDiff ℝ ∞ (fun x ↦ C x a j)) (k l j i : Fin n) :
    ∃ D > 0, ∀ (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
      (J : Fin n → Fin n → Fin n → Coord n → ℝ),
      (∀ a, MemLp (U a) 2 (volume.restrict K)) →
      (∀ a b, MemLp (H a b) 2 (volume.restrict K)) →
      (∀ a b c, MemLp (J a b c) 2 (volume.restrict K)) →
      ∀ E : ℝ, 0 ≤ E → (∀ a, (∫ x in K, (U a x)^2) ≤ E) →
      (∀ a b, (∫ x in K, (H a b x)^2) ≤ E) →
      (∀ a b c, (∫ x in K, (J a b c x)^2) ≤ E) →
        MemLp (realSecondCommutatorDerivative C U H J k l j i) 2 (volume.restrict K) ∧
        (∫ x in K, (realSecondCommutatorDerivative C U H J k l j i x)^2) ≤ D*E := by
  let A : Coord n → (Fin n × Fin 6) → ℝ := fun x t ↦
    let a := t.1
    ![coordPartial (fun y ↦ C y a j) x l,coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y l) x i,coordPartial (fun y ↦ C y a j) x k,coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x i,coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x l,coordPartial (fun y ↦ coordPartial (fun z ↦ coordPartial (fun t ↦ C t a j) z k) y l) x i] t.2
  have hA (t : Fin n × Fin 6) : Continuous (fun x ↦ A x t) := by
    rcases t with ⟨a,b⟩
    fin_cases b
    · exact (real_coordPartial_smooth _ (hC a j) l).continuous
    · exact (real_coordPartial_smooth _ (real_coordPartial_smooth _ (hC a j) l) i).continuous
    · exact (real_coordPartial_smooth _ (hC a j) k).continuous
    · exact (real_coordPartial_smooth _ (real_coordPartial_smooth _ (hC a j) k) i).continuous
    · exact (real_coordPartial_smooth _ (real_coordPartial_smooth _ (hC a j) k) l).continuous
    · exact (real_coordPartial_smooth _ (real_coordPartial_smooth _ (real_coordPartial_smooth _ (hC a j) k) l) i).continuous
  obtain ⟨D,hD,hb⟩ := real_compact_fintype_coefficient_common_bound hK A hA
  refine ⟨D,hD,fun U H J hU hH hJ E hE hUE hHE hJE ↦ ?_⟩
  let V : (Fin n × Fin 6) → Coord n → ℝ := fun t ↦
    let a := t.1
    ![J a k i,H a k,J a l i,H a l,H a i,U a] t.2
  have hV (t : Fin n × Fin 6) : MemLp (V t) 2 (volume.restrict K) := by
    rcases t with ⟨a,b⟩
    fin_cases b
    · exact hJ a k i
    · exact hH a k
    · exact hJ a l i
    · exact hH a l
    · exact hH a i
    · exact hU a
  have hVE (t : Fin n × Fin 6) : (∫ x in K, (V t x)^2) ≤ E := by
    rcases t with ⟨a,b⟩
    fin_cases b
    · exact hJE a k i
    · exact hHE a k
    · exact hJE a l i
    · exact hHE a l
    · exact hHE a i
    · exact hUE a
  have h := hb V hV E hE hVE
  have heq : (fun x ↦ ∑ t, A x t*V t x)=realSecondCommutatorDerivative C U H J k l j i := by
    funext x
    simp [A,V,realSecondCommutatorDerivative,Fintype.sum_prod_type,Fin.sum_univ_succ,add_assoc]
  rw [heq] at h
  simp_rw [show ∀ x, _ = _ from fun x ↦ congrFun heq x] at h
  exact h

end
end Yau

end OAI
