import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileLinearMap

namespace OAI

/-! Brouwer's theorem applied to the specific certified central linear map. -/

namespace DefocusingNLS.ProfileCertificate

theorem central_linear_injective : Function.Injective (realLinearMap centralX centralY) := by
  intro x y hxy
  have hz : realLinearMap centralX centralY (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  have hb := central_minimum_stretch (x-y)
  rw [hz, norm_zero] at hb
  have hn : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

noncomputable def centralLinearEquiv : ℂ ≃L[ℝ] ℂ :=
  (LinearEquiv.ofBijective (realLinearMap centralX centralY).toLinearMap
    ⟨central_linear_injective, LinearMap.injective_iff_surjective.mp central_linear_injective⟩).toContinuousLinearEquiv

@[simp] theorem centralLinearEquiv_apply (z : ℂ) :
    centralLinearEquiv z = realLinearMap centralX centralY z := rfl

theorem centralLinearEquiv_inverse_bound (z : ℂ) :
    ‖centralLinearEquiv.symm z‖ ≤ ‖z‖/(48/1000 : ℝ) := by
  have h := central_minimum_stretch (centralLinearEquiv.symm z)
  change (48/1000 : ℝ)*‖centralLinearEquiv.symm z‖ ≤ ‖centralLinearEquiv (centralLinearEquiv.symm z)‖ at h
  rw [centralLinearEquiv.apply_symm_apply] at h
  exact (le_div_iff₀ (by norm_num)).mpr (by nlinarith)

/-- The precise error margin needed to force a zero on the free-profile disk.
Continuity and the approximation are hypotheses on a finite-dimensional map,
not assumed statements about the NLS or its profiles. -/
theorem zero_of_free_profile_error
    (f : Metric.closedBall (0 : ℂ) (radius : ℝ) → ℂ) (hf : Continuous f)
    (herror : ∀ z, ‖f z-realLinearMap centralX centralY z.val‖ ≤ 25/1000000000000) :
    ∃ z, f z = 0 := by
  apply zero_of_near_invertible_linear_map centralLinearEquiv (radius : ℝ)
    ((25/1000000000000)/(48/1000)) (by norm_num [radius]) (by norm_num [radius]) f hf
  intro z
  have he : centralLinearEquiv.symm (f z)-z.val =
      centralLinearEquiv.symm (f z-centralLinearEquiv z.val) := by
    rw [map_sub, centralLinearEquiv.symm_apply_apply]
  rw [he]
  exact (centralLinearEquiv_inverse_bound _).trans
    ((div_le_div_iff_of_pos_right (by norm_num)).mpr (herror z))

end DefocusingNLS.ProfileCertificate

end OAI
