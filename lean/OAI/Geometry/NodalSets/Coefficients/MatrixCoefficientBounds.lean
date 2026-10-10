import Mathlib.Analysis.Calculus.ContDiff.Bounds
import OAI.Geometry.NodalSets.Coefficients.MatrixCoefficientMap

namespace OAI

namespace Yau.Target
open Matrix Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma matrixContravariant_add (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    matrixContravariant (A+B) = matrixContravariant A+matrixContravariant B := by
  ext α i
  simp [matrixContravariant,add_smul,Finset.sum_add_distrib]

def coefficientEntryLinear (i j : Fin 4) :
    ℝ →L[ℝ] ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight
    ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 4) ℝ j)).smulRight
      (EuclideanSpace.basisFun (Fin 4) ℝ i))

lemma matrixContravariant_entry_sum (A : Matrix (Fin 4) (Fin 4) ℝ) :
    matrixContravariant A = ∑ i, ∑ j, coefficientEntryLinear i j (A i j) := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma matrix_coefficient_derivative_bound
    (M : E → Matrix (Fin 4) (Fin 4) ℝ) (b : E → ℝ)
    (hM : ∀ j k, ContDiff ℝ ∞ (fun x ↦ M x j k)) (hb : ContDiff ℝ ∞ b)
    (x : E) (i : ℕ) {eps : ℝ} (heps : 0 ≤ eps)
    (hm : ∀ j k, ‖iteratedFDeriv ℝ i (fun y ↦ M y j k) x‖ ≤ eps)
    (hbnd : ‖iteratedFDeriv ℝ i b x‖ ≤ eps) :
    ‖iteratedFDeriv ℝ i (fun y ↦ (matrixContravariant (M y),b y)) x‖ ≤
      (1+∑ j, ∑ k, ‖coefficientEntryLinear j k‖)*eps := by
  let : IsBoundedSMul ℝ ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) :=
    IsBoundedSMul.of_norm_smul_le ContinuousLinearMap.opNorm_smul_le
  have hs (j k : Fin 4) : ContDiff ℝ ∞ (fun y ↦ coefficientEntryLinear j k (M y j k)) :=
    (hM j k).smul contDiff_const
  have hmat : ContDiff ℝ ∞ (fun y ↦ matrixContravariant (M y)) := by
    simp_rw [matrixContravariant_entry_sum]
    exact ContDiff.sum (fun j _ ↦ ContDiff.sum (fun k _ ↦ hs j k))
  have hbound : ‖iteratedFDeriv ℝ i (fun y ↦ matrixContravariant (M y)) x‖ ≤
      (∑ j, ∑ k, ‖coefficientEntryLinear j k‖)*eps := by
    simp_rw [matrixContravariant_entry_sum]
    rw [iteratedFDeriv_fun_sum_apply (fun j _ ↦
      (ContDiff.sum (fun k _ ↦ hs j k)).contDiffAt.of_le (show (i : ℕ∞ω) ≤ ∞ by exact_mod_cast (show (i : ℕ∞) ≤ ⊤ from le_top)))]
    refine (norm_sum_le _ _).trans ?_
    simp_rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [iteratedFDeriv_fun_sum_apply (fun k _ ↦ (hs j k).contDiffAt.of_le (show (i : ℕ∞ω) ≤ ∞ by exact_mod_cast (show (i : ℕ∞) ≤ ⊤ from le_top)))]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro k _
    change ‖iteratedFDeriv ℝ i (fun y ↦ M y j k • ((ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.basisFun (Fin 4) ℝ k)).smulRight (EuclideanSpace.basisFun (Fin 4) ℝ j))) x‖ ≤ _
    rw [iteratedFDeriv_smul_const_apply ((hM j k).of_le
      (by exact_mod_cast (show (i : ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
    exact ((coefficientEntryLinear j k).norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul_of_nonneg_left (hm j k) (norm_nonneg _))
  rw [iteratedFDeriv_prodMk hmat.contDiffAt hb.contDiffAt (by exact_mod_cast (show (i : ℕ∞) ≤ ⊤ from le_top))]
  have hn : 0 ≤ ∑ j, ∑ k, ‖coefficientEntryLinear j k‖ :=
    Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
  rw [ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · exact hbound.trans (by nlinarith)
  · exact hbnd.trans (by nlinarith)

end
end Yau.Target

end OAI
