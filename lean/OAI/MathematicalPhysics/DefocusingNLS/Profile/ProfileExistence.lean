import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileTailError
import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileQuotientContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileZeroCriterion

namespace OAI

/-! A zero of the actual free-profile matching quotient in the certified disk. -/

namespace DefocusingNLS.ProfileCertificate

theorem diskProfile_linear_error (w : Metric.closedBall (0 : ℂ) (radius : ℝ)) :
    ‖diskProfile w-realLinearMap centralX centralY w.val‖ < (25/1000000000000 : ℝ) := by
  obtain ⟨hb, hz⟩ := disk_coordinates w
  simpa only [diskProfile, realLinearMap_apply] using
    free_profile_linear_error w.val.re w.val.im hb hz

theorem diskProfile_bound (w : Metric.closedBall (0 : ℂ) (radius : ℝ)) :
    ‖diskProfile w‖ < (3/1000000000 : ℝ) := by
  obtain ⟨hb, hz⟩ := disk_coordinates w
  have he := diskProfile_linear_error w
  have hl := free_linear_size w.val.re w.val.im hb hz
  rw [← realLinearMap_apply] at hl
  have hc := (Rat.cast_lt (K := ℝ)).mpr propagation_comparisons.2.2.2.1
  push_cast at hc
  have hn : ‖diskProfile w‖ ≤
      ‖diskProfile w-realLinearMap centralX centralY w.val‖+
        ‖realLinearMap centralX centralY w.val‖ := by
    calc
      _ = ‖(diskProfile w-realLinearMap centralX centralY w.val)+
          realLinearMap centralX centralY w.val‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  linarith

theorem diskProfile_boundary_margin (w : Metric.closedBall (0 : ℂ) (radius : ℝ))
    (hw : ‖w.val‖ = (radius : ℝ)) :
    (91/200000000000 : ℝ) < ‖diskProfile w‖ := by
  have hl := central_minimum_stretch w.val
  rw [hw] at hl
  have he := diskProfile_linear_error w
  have hn := norm_sub_norm_le (realLinearMap centralX centralY w.val) (diskProfile w)
  rw [norm_sub_rev] at hn
  have hc : (48/1000 : ℝ)*(radius : ℝ) = (48/100000000000 : ℝ) := by norm_num [radius]
  rw [hc] at hl
  linarith

/-- The certified error and Brouwer's theorem give an actual free matching root. -/
theorem exists_diskProfile_zero :
    ∃ w : Metric.closedBall (0 : ℂ) (radius : ℝ),
      ‖w.val‖ < (radius : ℝ) ∧ diskProfile w = 0 := by
  obtain ⟨w, hw⟩ := zero_of_free_profile_error diskProfile continuous_diskProfile
    (fun w => (diskProfile_linear_error w).le)
  refine ⟨w, ?_, hw⟩
  have hn : ‖w.val‖ ≤ (radius : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using w.property
  apply lt_of_le_of_ne hn
  intro he
  have hm := diskProfile_boundary_margin w he
  rw [hw, norm_zero] at hm
  norm_num at hm

/-- The free matching condition is the vanishing of the actual spatial derivative. -/
theorem freeProfileJ_eq_log_derivative (b Z : ℝ) (hZ : 0 < Z) :
    freeProfileJ b Z =
      -deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6) (-Complex.I*(Z : ℂ))/
        regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ)) := by
  have h := (hasDerivAt_regularizedSlowSolution_shift_closed
    (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ))
    (by simp) (by simp) (by simpa using hZ.ne')).deriv
  rw [h]
  unfold freeProfileJ
  ring

theorem exists_free_profile_matching :
    ∃ b Z : ℝ, (b-(centerB : ℝ))^2+(Z-(centerZ : ℝ))^2 < (radius : ℝ)^2 ∧
      regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ)) ≠ 0 ∧
      deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6) (-Complex.I*(Z : ℂ)) = 0 := by
  obtain ⟨w, hwn, hw⟩ := exists_diskProfile_zero
  obtain ⟨hb, hz⟩ := disk_coordinates w
  refine ⟨(centerB : ℝ)+w.val.re, (centerZ : ℝ)+w.val.im, ?_, ?_, ?_⟩
  · have hsq := (sq_lt_sq₀ (norm_nonneg w.val) (by norm_num [radius])).mpr hwn
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hsq
    simpa only [add_sub_cancel_left, pow_two] using hsq
  · simpa only [neg_mul] using free_profile_nonzero w.val.re w.val.im hb hz
  · have hZ : 0 < (centerZ : ℝ)+w.val.im := by
      have hz' := (abs_le.mp hz).1
      norm_num [centerZ, radius] at hz' ⊢
      linarith
    change freeProfileJ ((centerB : ℝ)+w.val.re) ((centerZ : ℝ)+w.val.im) = 0 at hw
    rw [freeProfileJ_eq_log_derivative _ _ hZ] at hw
    have hn := free_profile_nonzero w.val.re w.val.im hb hz
    simp only [neg_mul] at hn
    simp only [neg_mul] at hw ⊢
    exact neg_eq_zero.mp ((div_eq_zero_iff.mp hw).resolve_right hn)

end DefocusingNLS.ProfileCertificate

end OAI
