import Mathlib
import OAI.Analysis.WeakInfiniteness.FourColumnNorm
import OAI.Analysis.WeakInfiniteness.NonunitalSpectralTools2
import OAI.Analysis.WeakInfiniteness.SupportedCorner

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

open scoped CStarAlgebra

section

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma map_positive_sqrt (φ : A →⋆ₙₐ[ℂ] B) {a : A} (ha : 0 ≤ a) :
    φ (CFC.sqrt a)=CFC.sqrt (φ a) := by
  symm
  apply CFC.sqrt_unique
  · rw [← map_mul,CFC.sqrt_mul_sqrt_self a ha]
  · exact map_nonneg φ (CFC.sqrt_nonneg a)

lemma norm_column_le_sqrt_sum (x y : A) : ‖x‖ ≤ ‖CFC.sqrt (x*star x+y*star y)‖ := by
  have hxy : 0 ≤ x*star x+y*star y := add_nonneg (mul_star_self_nonneg x) (mul_star_self_nonneg y)
  have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (le_add_of_nonneg_right (mul_star_self_nonneg y)) (mul_star_self_nonneg x)
  have he : ‖CFC.sqrt (x*star x+y*star y)‖^2=‖x*star x+y*star y‖ := by
    rw [pow_two,← CStarRing.norm_star_mul_self,(CFC.sqrt_nonneg _).star_eq,CFC.sqrt_mul_sqrt_self _ hxy]
  rw [CStarRing.norm_self_mul_star] at h
  nlinarith [norm_nonneg x,norm_nonneg (CFC.sqrt (x*star x+y*star y))]

lemma norm_other_column_le_sqrt_sum (x y : A) : ‖y‖ ≤ ‖CFC.sqrt (x*star x+y*star y)‖ := by
  simpa only [add_comm] using norm_column_le_sqrt_sum y x

local instance matrixRealModuleFourAssembly {j : Type*} [Fintype j] :
    Module ℝ (CStarMatrix j j A) := Module.complexToReal _

def twoEntryRow (x y : A) : CStarMatrix (Fin 1) (Fin 2) A := fun _ j => ![x,y] j

omit [PartialOrder A] [StarOrderedRing A] in
lemma twoEntryRow_range (x y : A) :
    matrixSingletonHom (twoEntryRow x y*(twoEntryRow x y).conjTranspose)=x*star x+y*star y := by
  change (∑ i : Fin 2, (![x,y] i)*star (![x,y] i))=x*star x+y*star y
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]

lemma norm_two_sqrt_sums_le (x₀ x₁ y₀ y₁ : A) :
    ‖CFC.sqrt (x₀*star x₀+x₁*star x₁)*CFC.sqrt (y₀*star y₀+y₁*star y₁)‖ ≤
      ‖star x₀*y₀‖+‖star x₁*y₀‖+‖star x₀*y₁‖+‖star x₁*y₁‖ := by
  let U := twoEntryRow x₀ x₁
  let V := twoEntryRow y₀ y₁
  have hU : 0 ≤ U*U.conjTranspose := by
    simpa only [rectangular_conjTranspose_conjTranspose] using rectangular_initial_nonneg U.conjTranspose
  have hV : 0 ≤ V*V.conjTranspose := by
    simpa only [rectangular_conjTranspose_conjTranspose] using rectangular_initial_nonneg V.conjTranspose
  have hsU := map_positive_sqrt (matrixSingletonHom (A := A)) hU
  have hsV := map_positive_sqrt (matrixSingletonHom (A := A)) hV
  have hnorm := NonUnitalStarAlgHom.norm_map (matrixSingletonHom (A := A)) matrixSingletonHom_injective
    (CFC.sqrt (U*U.conjTranspose)*CFC.sqrt (V*V.conjTranspose))
  rw [map_mul,hsU,hsV,twoEntryRow_range,twoEntryRow_range] at hnorm
  rw [hnorm,norm_rectangular_range_roots]
  apply (norm_matrix_le_sum_entries _).trans_eq
  change (∑ j : Fin 2,∑ i : Fin 2, ‖(∑ k : Fin 1,star (![x₀,x₁] i)*(![y₀,y₁] j))‖)=_
  simp only [Fin.sum_univ_two,Fin.sum_univ_one,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

end

section

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma inr_snd_inr_mul (a : A) (u : Unitization ℂ A) :
    (((a : Unitization ℂ A)*u).snd : Unitization ℂ A)=(a : Unitization ℂ A)*u := by
  apply unitization_inr_snd_of_fst_eq_zero
  simp only [Unitization.fst_mul,Unitization.fst_inr,zero_mul]

lemma unitizedRight_mem_principal (a : A) (ha : 0 ≤ a) (u : Unitization ℂ A) :
    ((a : Unitization ℂ A)*u).snd ∈ principalRightIdeal a := by
  have haself : a ∈ principalRightIdeal a := hereditary_le_rightIdeal a ha.isSelfAdjoint
    (self_mem_hereditary a ha)
  change (0 : ℂ) • u.snd+u.fst • a+a*u.snd ∈ principalRightIdeal a
  rw [zero_smul,zero_add]
  exact (principalRightIdeal a).add_mem ((principalRightIdeal a).smul_mem _ haself)
    (Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (LinearMap.mulLeft ℂ a) u.snd))

lemma norm_sqrt_sum_representation {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (π : A →⋆ₙₐ[ℂ] B) (x y : A) :
    ‖π x‖ ≤ ‖π (CFC.sqrt (x*star x+y*star y))‖ ∧
      ‖π y‖ ≤ ‖π (CFC.sqrt (x*star x+y*star y))‖ := by
  rw [map_positive_sqrt π (add_nonneg (mul_star_self_nonneg x) (mul_star_self_nonneg y)),
    map_add,map_mul,map_mul,map_star,map_star]
  exact ⟨norm_column_le_sqrt_sum _ _,norm_other_column_le_sqrt_sum _ _⟩

end

end

end WeakPureInfiniteness
end

end OAI
