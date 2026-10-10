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

section

variable {A : Type u} [NonUnitalCStarAlgebra A]

variable {n : ℕ}

def finiteCoefficientSum (v : Fin n → A) (M : CStarMatrix (Fin n) (Fin n) ℂ) : A :=
  ∑ i,∑ j,M i j • (star (v i)*v j)

def matrixCoefficientWeight (M : CStarMatrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i,∑ j,‖M i j‖

lemma matrixCoefficientWeight_nonneg (M : CStarMatrix (Fin n) (Fin n) ℂ) :
    0 ≤ matrixCoefficientWeight M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma matrixCoefficientWeight_one : matrixCoefficientWeight (1:CStarMatrix (Fin n) (Fin n) ℂ)=n := by
  simp [matrixCoefficientWeight,CStarMatrix.one_apply,apply_ite]

lemma finiteCoefficientSum_one (v : Fin n → A) :
    finiteCoefficientSum v 1=∑ i,star (v i)*v i := by
  simp [finiteCoefficientSum,CStarMatrix.one_apply]

lemma finiteCoefficientSum_gram_error
    (ψ : CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] A) (v : Fin n → A)
    (η : ℝ) (hv : ∀ i j,‖star (v i)*v j-ψ (matrixUnit i j)‖≤η)
    (M : CStarMatrix (Fin n) (Fin n) ℂ) :
    ‖finiteCoefficientSum v M-ψ M‖≤η*matrixCoefficientWeight M := by
  have he : finiteCoefficientSum v M-ψ M=
      ∑ i,∑ j,M i j • (star (v i)*v j-ψ (matrixUnit i j)) := by
    conv_lhs => arg 2; rw [← matrix_unit_expansion M]
    simp only [map_sum,map_smul,finiteCoefficientSum,smul_sub,Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ i,∑ j,‖M i j • (star (v i)*v j-ψ (matrixUnit i j))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i,∑ j,‖M i j‖*η := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hv i j) (norm_nonneg _)
    _ = _ := by simp only [matrixCoefficientWeight,← Finset.sum_mul]; ring

lemma finiteCoefficientSum_rescale (v : Fin n → A) (κ : ℝ) (hκ : 0≤κ)
    (M : CStarMatrix (Fin n) (Fin n) ℂ) :
    finiteCoefficientSum (fun i => (Real.sqrt κ:ℂ) • v i) M=
      (κ:ℂ) • finiteCoefficientSum v M := by
  have he (i j : Fin n) :
      star ((Real.sqrt κ:ℂ) • v i)*((Real.sqrt κ:ℂ) • v j)=
        (κ:ℂ) • (star (v i)*v j) := by
    simp only [star_smul,Complex.star_def,Complex.conj_ofReal,smul_mul_assoc,mul_smul_comm,smul_smul]
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt hκ]
  simp only [finiteCoefficientSum,he,smul_comm (M _ _) (κ:ℂ),Finset.smul_sum]

lemma finiteCoefficientSum_rescale_error
    (v : Fin n → A) (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1)
    (ψ : CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] A)
    (M : CStarMatrix (Fin n) (Fin n) ℂ) :
    ‖finiteCoefficientSum (fun i => (Real.sqrt κ:ℂ) • v i) M-ψ M‖≤
      ‖finiteCoefficientSum v M-ψ M‖+(1-κ)*‖ψ M‖ := by
  rw [finiteCoefficientSum_rescale v κ hκ M]
  have he : (κ:ℂ) • finiteCoefficientSum v M-ψ M=
      (κ:ℂ) • (finiteCoefficientSum v M-ψ M)+((κ:ℂ)-1) • ψ M := by
    rw [smul_sub,sub_smul,one_smul]
    abel
  rw [he]
  calc
    _ ≤ ‖(κ:ℂ) • (finiteCoefficientSum v M-ψ M)‖+‖((κ:ℂ)-1) • ψ M‖ := norm_add_le _ _
    _ = κ*‖finiteCoefficientSum v M-ψ M‖+(1-κ)*‖ψ M‖ := by
      rw [norm_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hκ]
      have hnorm : ‖(κ:ℂ)-1‖=1-κ := by
        rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonpos (by linarith)]
        ring
      rw [hnorm]
    _ ≤ _ := add_le_add (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hκ1 (norm_nonneg (finiteCoefficientSum v M-ψ M))) le_rfl

end

end

end WeakPureInfiniteness
end

end OAI
