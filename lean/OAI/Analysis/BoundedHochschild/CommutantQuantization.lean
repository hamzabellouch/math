import Mathlib
import OAI.Analysis.BoundedHochschild.MatrixCommutants
import OAI.Analysis.BoundedHochschild.MatrixDisplacement

namespace OAI

/-! Small matrix expectations and coefficient energy bounds. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildQuantization
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {I : Type v} [Fintype I]

def matrixEnergy (x : I → M) {n : ℕ} (E : MatrixSystem M n) : ℝ :=
  ∑ i, ‖τ.toPreGNS (E.expectation (x i))‖^2

lemma matrixEnergy_nonneg (x : I → M) {n : ℕ} (E : MatrixSystem M n) :
    0 ≤ matrixEnergy τ x E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma matrixEnergy_drop (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (x : I → M) {n m : ℕ} (E : MatrixSystem M n) (F : MatrixSystem E.commutant m)
    (hn : n ≠ 0) (hm : m ≠ 0) (i : I) {δ : ℝ}
    (hi : ‖τ.toPreGNS ((E.extend F).expectation (x i))‖^2+δ <
      ‖τ.toPreGNS (E.expectation (x i))‖^2) :
    matrixEnergy τ x (E.extend F)+δ < matrixEnergy τ x E := by
  classical
  have hh : (∑ j ∈ Finset.univ.erase i, ‖τ.toPreGNS ((E.extend F).expectation (x j))‖^2) ≤
      ∑ j ∈ Finset.univ.erase i, ‖τ.toPreGNS (E.expectation (x j))‖^2 := by
    apply Finset.sum_le_sum
    intro j hj
    have hp := E.extension_pythagoras F τ htr hn hm (x j)
    nlinarith [sq_nonneg ‖τ.toPreGNS (E.expectation (x j)-(E.extend F).expectation (x j))‖]
  have hE := Finset.sum_erase_add Finset.univ
    (fun j => ‖τ.toPreGNS (E.expectation (x j))‖^2) (Finset.mem_univ i)
  have hF := Finset.sum_erase_add Finset.univ
    (fun j => ‖τ.toPreGNS ((E.extend F).expectation (x j))‖^2) (Finset.mem_univ i)
  dsimp only [matrixEnergy]
  linarith

include e in
 

theorem exists_small_matrix_expectations
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (x : I → M) (hx : ∀ i, τ (x i)=0) {ε : ℝ} (hε : 0<ε) :
    ∃ (n : ℕ) (E : MatrixSystem M n), 0<n ∧ ∀ i, ‖τ.toPreGNS (E.expectation (x i))‖<ε := by
  classical
  let S : Set ℝ := {b | ∃ (n : ℕ) (E : MatrixSystem M n), 0<n ∧ b=matrixEnergy τ x E}
  have hS : S.Nonempty := by
    obtain ⟨E⟩ := exists_matrixSystem e τ hτ htr hfaith h1 hfactor hdiff 1 (by omega)
    exact ⟨matrixEnergy τ x E,1,E,by omega,rfl⟩
  have hSb : BddBelow S := ⟨0,by
    rintro b ⟨n,E,hn,rfl⟩
    exact matrixEnergy_nonneg τ x E⟩
  let δ : ℝ := (ε/32)^2
  have hδ : 0<δ := sq_pos_of_pos (div_pos hε (by norm_num))
  obtain ⟨b,hbS,hb⟩ := exists_lt_of_csInf_lt hS (lt_add_of_pos_right (sInf S) hδ)
  obtain ⟨n,E,hn,rfl⟩ := hbS
  refine ⟨n,E,hn,?_⟩
  intro i
  by_contra hi
  have hei : ε ≤ ‖τ.toPreGNS (E.expectation (x i))‖ := le_of_not_gt hi
  have hecenter : E.expectation (x i)-(τ (x i)) • (1:M)=E.expectation (x i) := by
    rw [hx i,zero_smul,sub_zero]
  have hp : 0<‖τ.toPreGNS (E.expectation (x i)-(τ (x i)) • (1:M))‖ := by
    rw [hecenter]; exact hε.trans_le hei
  obtain ⟨m,F,hm,hdrop⟩ := E.exists_energy_decreasing_extension e τ hn hτ h1 htr hfaith
    hfactor hdiff (x i) hp
  rw [hecenter] at hdrop
  have hd : δ ≤ (‖τ.toPreGNS (E.expectation (x i))‖/32)^2 := by
    dsimp [δ]
    exact (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
  have hd' := matrixEnergy_drop τ htr x E F (Nat.ne_of_gt hn) (Nat.ne_of_gt hm) i
    (lt_of_le_of_lt (add_le_add_right hd _) hdrop)
  have hnew : matrixEnergy τ x (E.extend F) ∈ S :=
    ⟨n*m,E.extend F,Nat.mul_pos hn hm,rfl⟩
  have hlo := csInf_le hSb hnew
  linarith

end HochschildQuantization

 

 

open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
variable {M : Type*} [CStarAlgebra M]
variable {n : ℕ} (E : MatrixSystem M n)

lemma coefficient_product_matrix (i l : Fin n) (x y : M) :
    E.coefficient i l (x*y)=∑ j, E.coefficient i j x*E.coefficient j l y := by
  classical
  symm
  calc
    _ = ∑ j,∑ k, E.entry k i*x*(E.entry j j*y*E.entry l k) := by
      apply Finset.sum_congr rfl
      intro j hj
      change (∑ k,E.entry k i*x*E.entry j k)*E.coefficient j l y=_
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [mul_assoc,E.entry_mul_coefficient]
    _ = ∑ k, E.entry k i*x*((∑ j,E.entry j j)*y*E.entry l k) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]
    _ = _ := by simp only [E.sum_diagonal,one_mul,coefficient,mul_assoc]

lemma sum_coefficient_diagonal (hn : n ≠ 0) (x : M) :
    (∑ i,E.coefficient i i x)=(n:ℂ) • E.expectation x := by
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [coefficient,expectation_apply,smul_smul,mul_inv_cancel₀ hnC,one_smul]
  exact Finset.sum_comm

variable [PartialOrder M] [StarOrderedRing M]

lemma coefficient_norm_sq_sum (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0) (x : M) :
    (∑ i,∑ j, ‖τ.toPreGNS (E.coefficient i j x)‖^2)=(n:ℝ)*‖τ.toPreGNS x‖^2 := by
  have hh : (∑ i,∑ j,τ (star (E.coefficient j i x)*E.coefficient j i x))=
      (n:ℂ)*τ (star x*x) := by
    simp only [E.coefficient_star,← map_sum,← E.coefficient_product_matrix]
    rw [E.sum_coefficient_diagonal hn,map_smul,smul_eq_mul,E.trace_expectation τ htr hn]
  have hr := congrArg Complex.re hh
  simp only [Complex.re_sum,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] at hr
  simp only [norm_sq]
  rw [Finset.sum_comm]
  exact hr

omit [StarOrderedRing M] in
lemma trace_entry_commutant (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0) (c : M)
    (hc : c ∈ E.commutant) (i j : Fin n) :
    τ (E.entry i j*c)=if i=j then (n:ℂ)⁻¹*τ c else 0 := by
  classical
  have hcyc (k : Fin n) : τ (E.entry k k*c)=τ (E.entry i i*c) := by
    calc
      _ = τ (E.entry k i*(E.entry i k*c)) := by rw [← mul_assoc,E.entry_mul,ite_eq_left rfl]
      _ = τ ((E.entry i k*c)*E.entry k i) := htr _ _
      _ = _ := by rw [mul_assoc,(hc k i).eq,← mul_assoc,E.entry_mul,ite_eq_left rfl]
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl]
    have hh : (n:ℂ)*τ (E.entry i i*c)=τ c := by
      calc
        _ = ∑ k,τ (E.entry k k*c) := by
          simp only [hcyc,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        _ = τ c := by rw [← map_sum,← Finset.sum_mul,E.sum_diagonal,one_mul]
    have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
    rw [← hh,← mul_assoc,inv_mul_cancel₀ hnC,one_mul]
  · rw [ite_eq_right hij]
    calc
      _ = τ (E.entry i j*(E.entry j j*c)) := by rw [← mul_assoc,E.entry_mul,ite_eq_left rfl]
      _ = τ ((E.entry j j*c)*E.entry i j) := htr _ _
      _ = 0 := by rw [mul_assoc,(hc i j).eq,← mul_assoc,E.entry_mul,ite_eq_right (Ne.symm hij),zero_mul,map_zero]

end MatrixSystem
end HochschildMatrixSystems
end

end OAI
