import OAI.Analysis.HilbertCrouzeix.NumericalRange

namespace OAI

noncomputable section

open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate

namespace HilbertCrouzeix

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Elementary
omit [CompleteSpace H]

theorem lowerBound_of_unit_inner (T : H →L[ℂ] H) {δ : ℝ}
    (h : ∀ x : H, ‖x‖ = 1 → δ ≤ ‖inner ℂ x (T x)‖) (x : H) :
    δ * ‖x‖ ≤ ‖T x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let y : H := (‖x‖ : ℂ)⁻¹ • x
  have hy : ‖y‖ = 1 := norm_smul_inv_norm hx
  have hl : δ ≤ ‖T y‖ := calc
    δ ≤ ‖inner ℂ y (T y)‖ := h y hy
    _ ≤ ‖y‖ * ‖T y‖ := norm_inner_le_norm _ _
    _ = ‖T y‖ := by rw [hy, one_mul]
  calc
    δ * ‖x‖ ≤ ‖T y‖ * ‖x‖ := mul_le_mul_of_nonneg_right hl (norm_nonneg x)
    _ = ‖T x‖ := by
      simp only [y, map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_norm]
      field_simp

theorem antilipschitz_of_lowerBound (T : H →L[ℂ] H) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x : H, δ * ‖x‖ ≤ ‖T x‖) :
    AntilipschitzWith ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩ T := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [dist_eq_norm]
  change ‖x - y‖ ≤ δ⁻¹ * ‖T x - T y‖
  rw [← map_sub, inv_mul_eq_div]
  exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using h (x - y))

end Elementary

theorem isUnit_of_unit_inner (T : H →L[ℂ] H) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x : H, ‖x‖ = 1 → δ ≤ ‖inner ℂ x (T x)‖) : IsUnit T := by
  have hl := antilipschitz_of_lowerBound T hδ (lowerBound_of_unit_inner T h)
  have hadj : ∀ x : H, ‖x‖ = 1 → δ ≤ ‖inner ℂ x (T.adjoint x)‖ := by
    intro x hx
    rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
    exact h x hx
  have hla := antilipschitz_of_lowerBound T.adjoint hδ
    (lowerBound_of_unit_inner T.adjoint hadj)
  have hc : IsClosed (T.toLinearMap.range : Set H) := hl.isClosed_range T.uniformContinuous
  have hbot : T.toLinearMap.rangeᗮ = ⊥ := by
    rw [T.orthogonal_range]
    exact LinearMap.ker_eq_bot.mpr hla.injective
  have htop : T.toLinearMap.range = ⊤ := by
    rw [← hc.submodule_topologicalClosure_eq]
    exact Submodule.topologicalClosure_eq_top_iff.mpr hbot
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hl.injective, LinearMap.range_eq_top.mp htop⟩

theorem spectrum_subset_numericalClosure (A : H →L[ℂ] H) :
    spectrum ℂ A ⊆ numericalClosure A := by
  intro z hz
  by_contra hnot
  obtain ⟨δ, hδ, hb⟩ := Metric.isOpen_iff.mp
    (isClosed_closure.isOpen_compl) z hnot
  have hdist : ∀ w ∈ numericalRange A, δ ≤ ‖z - w‖ := by
    intro w hw
    by_contra! hlt
    have hw' : w ∈ Metric.ball z δ := by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hlt
    exact hb hw' (subset_closure hw)
  have hu : IsUnit ((algebraMap ℂ (H →L[ℂ] H)) z - A) := by
    apply isUnit_of_unit_inner _ hδ
    intro x hx
    simpa only [sub_apply, ContinuousLinearMap.algebraMap_apply,
      inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hx,
      RCLike.ofReal_one, one_pow, mul_one] using
      hdist (inner ℂ x (A x)) ⟨x, hx, rfl⟩
  exact spectrum.mem_iff.mp hz hu

theorem numericalClosure_geometry (A : H →L[ℂ] H) :
    IsCompact (numericalClosure A) ∧ Convex ℝ (numericalClosure A) ∧
      spectrum ℂ A ⊆ numericalClosure A :=
  ⟨isCompact_numericalClosure A, convex_numericalClosure A, spectrum_subset_numericalClosure A⟩


end HilbertCrouzeix

end

end OAI
