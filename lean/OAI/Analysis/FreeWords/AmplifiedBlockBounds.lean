import Mathlib
import OAI.Analysis.FreeWords.AmplifiedBlockBoundsDefinitions
import OAI.Analysis.FreeWords.MatrixUnitaryBounds

namespace OAI

noncomputable section

namespace KKMatrixBounds

noncomputable section

open KKHaarEndpoints KKMatrixExpectation Filter

open scoped Matrix.Norms.Operator Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem wordBound_nonneg (n:ℕ) (w:List (ℤ×Matrix (Fin n) (Fin n) A)) :
    0≤wordBound n w := by
  induction w with
  | nil => simp [wordBound]
  | cons z w ih =>
    change 0≤((n:ℝ)*‖z.2‖)*wordBound n w
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) ih

theorem powerWord_norm_le (n:ℕ) (U:unitary (Matrix (Fin n) (Fin n) A))
    (w:List (ℤ×Matrix (Fin n) (Fin n) A)) :
    ‖powerWord U w‖≤wordBound n w := by
  induction w with
  | nil =>
    change ‖(1:Matrix (Fin n) (Fin n) A)‖≤1
    have h1 : ‖(1:A)‖≤1 := by
      have hh := CStarRing.norm_star_mul_self (x := (1:A))
      simp only [star_one,mul_one] at hh
      nlinarith [norm_nonneg (1:A)]
    rw [Matrix.linfty_opNorm_def]
    change ((Finset.univ.sup fun i:Fin n => ∑j:Fin n,‖(1:Matrix (Fin n) (Fin n) A) i j‖₊:NNReal):ℝ)≤((1:NNReal):ℝ)
    apply NNReal.coe_le_coe.mpr
    apply Finset.sup_le
    intro i hi
    have h1' : ‖(1:A)‖₊≤1 := h1
    simpa [Matrix.one_apply,apply_ite,eq_comm] using h1'
  | cons z w ih =>
    change ‖(U^z.1).val*z.2*powerWord U w‖≤((n:ℝ)*‖z.2‖)*wordBound n w
    calc
      _ ≤ ‖(U^z.1).val*z.2‖*‖powerWord U w‖ := norm_mul_le _ _
      _ ≤ ((n:ℝ)*‖z.2‖)*wordBound n w := by
        apply mul_le_mul
        · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (unitary_rowSum_norm_le (U^z.1)) (norm_nonneg _))
        · exact ih
        · exact norm_nonneg _
        · positivity

omit [PartialOrder A] [StarOrderedRing A] in
theorem expectation_tendsto_zero (ι:Type) (L:Filter ι) (τ:A →ₗ[ℂ] ℂ) (n:ℕ)
    (X:ι → Matrix (Fin n) (Fin n) A)
    (h:∀a b,Tendsto (fun j => τ (X j a b)) L (𝓝 0)) :
    Tendsto (fun j => matrixExpectation τ n (X j)) L (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  simpa only [matrixExpectation_apply,Pi.zero_apply,Matrix.zero_apply,map_zero,Function.comp_def] using
    ((continuous_algebraMap ℂ A).tendsto 0).comp (h a b)

theorem amplified_block_bounds : AmplifiedBlockBounds (A := A) :=
  ⟨powerWord_norm_le,expectation_tendsto_zero⟩

end

end KKMatrixBounds
end

end OAI
