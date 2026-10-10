import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileMatchingQuotient
import OAI.MathematicalPhysics.DefocusingNLS.Profile.FreeSlowContinuity

namespace OAI

/-! Continuity of the actual free-profile quotient on the certified disk. -/

namespace DefocusingNLS.ProfileCertificate

noncomputable def diskProfile (w : Metric.closedBall (0 : ℂ) (radius : ℝ)) : ℂ :=
  freeProfileJ ((centerB : ℝ)+w.val.re) ((centerZ : ℝ)+w.val.im)

theorem disk_coordinates (w : Metric.closedBall (0 : ℂ) (radius : ℝ)) :
    |w.val.re| ≤ (radius : ℝ) ∧ |w.val.im| ≤ (radius : ℝ) := by
  have h : ‖w.val‖ ≤ (radius : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using w.property
  exact ⟨(Complex.abs_re_le_norm _).trans h, (Complex.abs_im_le_norm _).trans h⟩

theorem continuous_diskProfile : Continuous diskProfile := by
  let p : Metric.closedBall (0 : ℂ) (radius : ℝ) → ℝ × ℝ :=
    fun w => ((centerB : ℝ)+w.val.re, (centerZ : ℝ)+w.val.im)
  have hp : Continuous p := by unfold p; fun_prop
  have hm : ∀ w, p w ∈ freeParameterRectangle := by
    intro w
    obtain ⟨hb, hz⟩ := disk_coordinates w
    dsimp [p, freeParameterRectangle]
    have hc : 0 ≤ (centerB : ℝ) := by norm_num [centerB]
    have hb' := (abs_add_le (centerB : ℝ) w.val.re).trans
      (add_le_add (le_of_eq (abs_of_nonneg hc)) hb)
    obtain ⟨hzl, hzu⟩ := abs_le.mp hz
    norm_num [centerB, centerZ, radius] at hb hb' hzl hzu ⊢
    exact ⟨by linarith, by linarith, by linarith⟩
  have h0 := (continuousOn_free_regularizedSlowSolution 0 (by norm_num) 6).comp_continuous hp hm
  have h1 := (continuousOn_free_regularizedSlowSolution 1 (by norm_num) 7).comp_continuous hp hm
  dsimp only [Function.comp_def] at h0 h1
  have hq : Continuous (fun w => freeShiftedQ 0 (p w)) := by
    unfold freeShiftedQ p
    fun_prop
  have he (w) : freeShiftedQ 1 (p w) = freeShiftedQ 0 (p w)+1 := by
    unfold freeShiftedQ
    push_cast
    ring
  simp_rw [he] at h1
  have hn (w) : regularizedSlowSolution (freeShiftedQ 0 (p w)) 6
      (freeSpatialArgument (p w)) ≠ 0 := by
    obtain ⟨hb, hz⟩ := disk_coordinates w
    simpa only [freeShiftedQ, freeSpatialArgument, p, Complex.ofReal_zero, zero_sub, neg_mul] using
      free_profile_nonzero w.val.re w.val.im hb hz
  convert! (hq.mul h1).div h0 hn using 1
  unfold diskProfile freeProfileJ freeShiftedQ freeSpatialArgument p
  funext w
  simp only [Pi.mul_apply, Pi.div_apply, Complex.ofReal_zero, zero_sub, neg_mul]

end DefocusingNLS.ProfileCertificate

end OAI
