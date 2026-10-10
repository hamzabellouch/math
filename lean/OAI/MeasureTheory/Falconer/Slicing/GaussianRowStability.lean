import OAI.MeasureTheory.Falconer.Slicing.GaussianKernelGeometry

namespace OAI

/-! # Quantitative kernel geometry near a fixed orthonormal row frame -/

namespace Falconer
open Set MeasureTheory
variable {d h : ℕ}

theorem gaussianRowMap_adjoint_apply (A : Fin h → Space d) (a : Space h) :
    (gaussianRowMap A).adjoint a = ∑ i, a i • A i := by
  calc
    _ = (gaussianRowMap A).adjoint
        (∑ i, a i • EuclideanSpace.basisFun (Fin h) ℝ i) := by
      congr 1
      exact (EuclideanSpace.basisFun (Fin h) ℝ).sum_repr a |>.symm
    _ = _ := by simp only [map_sum,map_smul,gaussianRowMap_adjoint_basis]

theorem row_adjoint_near_isometry (A : Fin h → Space d)
    (e : Space h →ₗᵢ[ℝ] Space d) {ε : ℝ}
    (hA : ∀ i, ‖A i-e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (a : Space h) :
    ‖(gaussianRowMap A).adjoint a-e a‖ ≤ (h:ℝ)*ε*‖a‖ := by
  have he : e a = ∑ i, a i • e (EuclideanSpace.basisFun (Fin h) ℝ i) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin h) ℝ).sum_repr a]
    simp only [map_sum,map_smul]
    rfl
  rw [gaussianRowMap_adjoint_apply,he,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin h, ‖a i • A i-a i • e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : Fin h, ‖a‖*ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [← smul_sub,norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le a i) (hA i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem row_adjoint_lower_near_isometry (A : Fin h → Space d)
    (e : Space h →ₗᵢ[ℝ] Space d) {ε : ℝ}
    (hA : ∀ i, ‖A i-e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (hε : (h:ℝ)*ε ≤ 1/2) (a : Space h) :
    ‖a‖ ≤ 2*‖(gaussianRowMap A).adjoint a‖ := by
  have h1 := row_adjoint_near_isometry A e hA a
  have h2 := norm_sub_norm_le (e a) ((gaussianRowMap A).adjoint a)
  rw [e.norm_map,norm_sub_rev] at h2
  have h3 := mul_le_mul_of_nonneg_right hε (norm_nonneg a)
  nlinarith

theorem kernel_projection_bound_of_adjoint_lower (L : Space d →L[ℝ] Space h)
    {K : ℝ} (hK : 0 ≤ K) (hL : ∀ a : Space h, ‖a‖ ≤ K*‖L.adjoint a‖)
    (x : Space d) : ‖L.kerᗮ.starProjection x‖ ≤ K*‖L x‖ := by
  let y := L.kerᗮ.starProjection x
  have hy : y ∈ L.kerᗮ := L.kerᗮ.starProjection_apply_mem x
  have hr : y ∈ L.adjoint.range := by
    rw [← ContinuousLinearMap.adjoint_toLinearMap,← LinearMap.orthogonal_ker]
    exact hy
  obtain ⟨a,ha⟩ := hr
  change L.adjoint a = y at ha
  have hnorm : ‖y‖^2 ≤ ‖a‖*‖L x‖ := by
    calc
      _ = inner ℝ y y := (real_inner_self_eq_norm_sq y).symm
      _ = inner ℝ (L.adjoint a) y := by rw [ha]
      _ = inner ℝ a (L y) := ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = inner ℝ a (L x) := congrArg (inner ℝ a)
        (linearMap_orthogonal_kernel_projection L x)
      _ ≤ _ := real_inner_le_norm _ _
  have hla := hL a
  rw [ha] at hla
  have hh := mul_le_mul_of_nonneg_right hla (norm_nonneg (L x))
  by_cases hz : ‖y‖ = 0
  · change ‖y‖ ≤ _
    rw [hz]
    exact mul_nonneg hK (norm_nonneg _)
  · have hp : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖y‖ ≤ _
    nlinarith

theorem row_kernel_projection_bound (A : Fin h → Space d)
    (e : Space h →ₗᵢ[ℝ] Space d) {ε : ℝ}
    (hA : ∀ i, ‖A i-e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (hε : (h:ℝ)*ε ≤ 1/2) (x : Space d) :
    ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ 2*‖gaussianRowMap A x‖ :=
  kernel_projection_bound_of_adjoint_lower _ (by norm_num)
    (row_adjoint_lower_near_isometry A e hA hε) x

end Falconer

end OAI
