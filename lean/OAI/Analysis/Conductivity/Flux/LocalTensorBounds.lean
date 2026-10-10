import Mathlib
import OAI.Analysis.Conductivity.Variational.LocalSymmetricPiola

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma matrix_three_product_norm_bound (A B : Mat3) : ‖A*B‖≤3*‖A‖*‖B‖ := by
  apply Matrix.norm_le_iff (by positivity) |>.mpr
  intro i j
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k : Fin 3,‖A i k*B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin 3,‖A‖*‖B‖ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
        (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem localPiolaTensor_linear_bound
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    {K : Set Coord3} (hK : IsCompact K) (hKs : K⊆X.source) :
    ∃ C : ℝ,0<C ∧ ∀ (B : Coord3 → Mat3),Function.support B⊆K → ∀ y,
      ‖localPiolaTensor X B y‖≤C*‖B (X.symm y)‖ := by
  classical
  let A : Coord3 → Mat3 := fun x => operatorMatrix (fderiv ℝ X x)
  let g : Coord3 → ℝ := fun x => 9*|(fderiv ℝ X x).det|⁻¹*‖A x‖*‖A x‖
  have hg : ContinuousOn g X.source := by
    intro x hx
    have hd : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fderiv ℝ X) x :=
      (hX.contDiffAt (X.open_source.mem_nhds hx)).fderiv_right (by simp)
    have hdM := (operatorMatrix_contDiff (m := Fin 3) (n := Fin 3)).contDiffAt.comp x hd
    have hd0 := local_fderiv_det_ne_zero X (hX.differentiableOn (by simp))
      (hXi.differentiableOn (by simp)) hx
    have hdet := ((contDiff_clm_det (E := Coord3) (↑(⊤ : ℕ∞))).contDiffAt.comp x hd).abs hd0
    exact (((continuousAt_const.mul ((hdet.inv (abs_ne_zero.mpr hd0)).continuousAt)).mul
      hdM.continuousAt.norm).mul hdM.continuousAt.norm).continuousWithinAt
  obtain ⟨D,hD⟩ := (hK.image_of_continuousOn (hg.mono hKs)).isBounded.exists_norm_le
  refine ⟨max D 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro B hsB y
  by_cases hy : y∈X.target
  · by_cases hxy : X.symm y∈K
    · have hbound : g (X.symm y)≤ max D 1 :=
        (le_abs_self _).trans ((hD _ (mem_image_of_mem _ hxy)).trans (le_max_left _ _))
      simp only [localPiolaTensor,ite_eq_left hy,norm_smul,Real.norm_eq_abs,abs_inv,abs_abs]
      calc
        _ ≤ |(fderiv ℝ X (X.symm y)).det|⁻¹ * (3*‖A (X.symm y)*B (X.symm y)‖*‖(A (X.symm y))ᵀ‖) :=
          mul_le_mul_of_nonneg_left (matrix_three_product_norm_bound _ _) (inv_nonneg.mpr (abs_nonneg _))
        _ ≤ |(fderiv ℝ X (X.symm y)).det|⁻¹ * (3*(3*‖A (X.symm y)‖*‖B (X.symm y)‖)*‖A (X.symm y)‖) := by
          rw [Matrix.norm_transpose]
          gcongr
          exact matrix_three_product_norm_bound _ _
        _ = g (X.symm y)*‖B (X.symm y)‖ := by dsimp [g]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    · have hz : B (X.symm y)=0 := by
        by_contra hn
        exact hxy (hsB hn)
      simp [localPiolaTensor,hy,hz]
  · simp only [localPiolaTensor,ite_eq_right hy,norm_zero]
    exact mul_nonneg ((le_max_right D 1).trans' zero_le_one) (norm_nonneg _)

end ScalarConductivity

end
end

end OAI
