import OAI.Dynamics.EntropyCounterexample.SphereCutoffsAffine

namespace OAI

noncomputable section

open Filter Topology

namespace Problem340.SphereCutoffs

theorem exists_fderiv_affinePreparationCutoff_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℂ, ‖fderiv ℝ affinePreparationCutoff z‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (hasCompactSupport_affinePreparationCutoff.fderiv ℝ).exists_bound_of_continuous
      ((@contDiff_affinePreparationCutoff 1).continuous_fderiv (by norm_num))
  exact ⟨max C 1, le_max_right _ _, fun z => (hC z).trans (le_max_left _ _)⟩

theorem exists_fderiv_bound_of_constant_tails (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (a b : ℝ)
    (hleft : ∀ x < -1, f x = a) (hright : ∀ x, 1 < x → f x = b) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
    (hf.continuous_fderiv (by norm_num)).continuousOn
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro x
  by_cases hl : x < -1
  · have heq : f =ᶠ[𝓝 x] (fun _ => a) := by
      filter_upwards [Iio_mem_nhds hl] with y hy
      exact hleft y hy
    rw [heq.fderiv_eq]
    simp only [fderiv_const_apply, norm_zero]
    exact (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_right _ _)
  by_cases hr : 1 < x
  · have heq : f =ᶠ[𝓝 x] (fun _ => b) := by
      filter_upwards [Ioi_mem_nhds hr] with y hy
      exact hright y hy
    rw [heq.fderiv_eq]
    simp only [fderiv_const_apply, norm_zero]
    exact (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_right _ _)
  exact (hC x ⟨le_of_not_gt hl, le_of_not_gt hr⟩).trans (le_max_left _ _)

private theorem exists_fderiv_bound_comp_linear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (A : E →L[ℝ] ℝ)
    (hbound : ∃ C : ℝ, 1 ≤ C ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ C) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x, ‖fderiv ℝ (f ∘ A) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := hbound
  refine ⟨max (C * ‖A‖) 1, le_max_right _ _, ?_⟩
  intro x
  rw [fderiv_comp x ((hf.differentiable (by norm_num)) (A x)) A.differentiableAt,
    A.fderiv]
  exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg A))).trans (le_max_left _ _)

theorem exists_fderiv_clockGateAmbient_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : SphereAmbient, ‖fderiv ℝ clockGateAmbient x‖ ≤ C := by
  let p : ℝ → ℝ := fun t => Real.smoothTransition ((25 * t + 15) / 8)
  have hp : ContDiff ℝ 1 p := by
    exact Real.smoothTransition.contDiff.comp
      (((contDiff_const.mul contDiff_id).add contDiff_const).div_const 8)
  have hb : ∃ C : ℝ, 1 ≤ C ∧ ∀ t, ‖fderiv ℝ p t‖ ≤ C := by
    apply exists_fderiv_bound_of_constant_tails p hp 0 1
    · intro t ht
      apply Real.smoothTransition.zero_of_nonpos
      linarith
    · intro t ht
      apply Real.smoothTransition.one_of_one_le
      linarith
  exact exists_fderiv_bound_comp_linear p hp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)) hb

theorem exists_fderiv_preparationCutoffAmbient_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : SphereAmbient,
      ‖fderiv ℝ preparationCutoffAmbient x‖ ≤ C := by
  let p : ℝ → ℝ := fun t => Real.smoothTransition (5 * t + 4) *
    Real.smoothTransition (1 - 2 * t)
  have hp : ContDiff ℝ 1 p := by
    exact (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).add contDiff_const)).mul
      (Real.smoothTransition.contDiff.comp
        (contDiff_const.sub (contDiff_const.mul contDiff_id)))
  have hb : ∃ C : ℝ, 1 ≤ C ∧ ∀ t, ‖fderiv ℝ p t‖ ≤ C := by
    apply exists_fderiv_bound_of_constant_tails p hp 0 0
    · intro t ht
      change Real.smoothTransition (5 * t + 4) * _ = 0
      rw [Real.smoothTransition.zero_of_nonpos (by linarith : 5 * t + 4 ≤ 0), zero_mul]
    · intro t ht
      change _ * Real.smoothTransition (1 - 2 * t) = 0
      rw [Real.smoothTransition.zero_of_nonpos (by linarith : 1 - 2 * t ≤ 0), mul_zero]
  exact exists_fderiv_bound_comp_linear p hp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)) hb

end Problem340.SphereCutoffs

end

end OAI
