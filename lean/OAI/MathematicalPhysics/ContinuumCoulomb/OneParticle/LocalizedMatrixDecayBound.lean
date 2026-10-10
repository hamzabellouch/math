import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCorrectedMatrixError

namespace OAI

/-! The shifted one-body matrix is itself small. Retaining this decay is
necessary when estimating the Gram correction after physical amplification. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarWellMatrix_uniform_bound (u v w : PlanarPosition) :
    |planarWellMatrix u v w| ≤ planarWellMatrixConstant := by
  simpa only [mul_zero,neg_zero,Real.exp_zero,mul_one] using
    planarWellMatrix_two_far (D := 0) u v w (norm_nonneg _) (norm_nonneg _)

theorem planarHoppingMatrix_decay {m : ℕ} (u : Fin m → PlanarPosition) {D : ℝ}
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (i j : Fin m) :
    |planarHoppingMatrix u i j| ≤
      (PlanarSobolev.wellBound*planarOverlapConstant)*Real.exp (-(9/10:ℝ)*D) := by
  classical
  unfold planarHoppingMatrix
  by_cases hij : i=j
  · simp only [hij,ite_true,abs_zero]
    exact mul_nonneg (mul_nonneg PlanarSobolev.wellBound_nonnegative
      planarOverlapConstant_nonnegative) (Real.exp_pos _).le
  · simp only [hij,ite_false]
    rw [← planarWellMatrix_hopping]
    exact (planarWellMatrix_overlap_decay (u i) (u j) (u i)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hsep i j hij]))
        (mul_nonneg PlanarSobolev.wellBound_nonnegative planarOverlapConstant_nonnegative))

theorem localizedCorrectedOneBodyMatrix_decay {freq D δ : ℝ}
    (hf : 0 < freq) (hD : 0 ≤ D) (hδ : 0 ≤ δ) (scale : ℝ)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (i j : Fin m) :
    |localizedCorrectedOneBodyMatrix freq scale u i j| ≤
      (PlanarSobolev.wellBound*planarOverlapConstant+(m:ℝ)*planarWellMatrixConstant)*
        Real.exp (-(9/10:ℝ)*D)+(m:ℝ)*δ*planarWellMatrixConstant := by
  have hC := planarWellMatrixConstant_nonnegative
  have hb : |localizedOneBodyMatrix freq u i j| ≤
      (PlanarSobolev.wellBound*planarOverlapConstant+(m:ℝ)*planarWellMatrixConstant)*
        Real.exp (-(9/10:ℝ)*D) := by
    have hsmall := localizedOneBodyMatrix_error_bound hf u hsep i j
    have hh := planarHoppingMatrix_decay u hsep i j
    have hexp : Real.exp (-(19/10:ℝ)*D) ≤ Real.exp (-(9/10:ℝ)*D) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ |localizedOneBodyMatrix freq u i j-planarHoppingMatrix u i j|+
          |planarHoppingMatrix u i j| := by
        simpa only [sub_zero] using abs_sub_le (localizedOneBodyMatrix freq u i j) (planarHoppingMatrix u i j) 0
      _ ≤ (m:ℝ)*planarWellMatrixConstant*Real.exp (-(9/10:ℝ)*D)+
          (PlanarSobolev.wellBound*planarOverlapConstant)*Real.exp (-(9/10:ℝ)*D) :=
        add_le_add (hsmall.trans (mul_le_mul_of_nonneg_left hexp (by positivity))) hh
      _ = _ := by ring
  have he : scale⁻¹*localizedCountertermMatrix freq u i j =
      ∑ k, (localizedCounterterm freq u k/scale)*planarWellMatrix (u i) (u j) (u k) := by
    simp only [localizedCountertermMatrix,Finset.mul_sum,div_eq_mul_inv]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hc : |scale⁻¹*localizedCountertermMatrix freq u i j| ≤ (m:ℝ)*δ*planarWellMatrixConstant := by
    rw [he]
    calc
      _ ≤ ∑ k, |(localizedCounterterm freq u k/scale)*planarWellMatrix (u i) (u j) (u k)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin m, δ*planarWellMatrixConstant := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul,abs_of_nonneg (hcoeff k).1]
        exact mul_le_mul (hcoeff k).2 (planarWellMatrix_uniform_bound _ _ _)
          (abs_nonneg _) hδ
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
  rw [localizedCorrectedOneBodyMatrix_eq hf]
  exact (abs_add_le _ _).trans (add_le_add hb hc)

end ContinuumCoulomb

end

end OAI
