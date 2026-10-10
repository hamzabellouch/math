import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeRadialRegularity
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeOutgoingSpectrum

namespace OAI

/-! An actual matched limiting profile with the complete free outgoing count. -/

namespace DefocusingNLS

theorem exists_free_limiting_model (hR : RectangleRouche) :
    ∃ b Z : ℝ, (b,Z) ∈ freeMatchingDisk ∧
      ContDiff ℝ 1 (freeRadialProfile b Z) ∧ freeRadialProfile b Z 0=1 ∧
      (∀ r : ℝ, 0 ≤ r → freeRadialProfile b Z r ≠ 0) ∧
      (∀ ell : ℕ, closedCountingHalfPlaneZeroCount (spectralSlowDeterminant ell b Z)=
        (freeOutgoingCount ell : ℕ∞)) := by
  obtain ⟨w,_,hw⟩ := ProfileCertificate.exists_diskProfile_zero
  let b : ℝ := (ProfileCertificate.centerB : ℝ)+w.val.re
  let Z : ℝ := (ProfileCertificate.centerZ : ℝ)+w.val.im
  obtain ⟨hb,hz⟩ := ProfileCertificate.disk_coordinates w
  have hZ : 0 < Z := by
    have hl := (abs_le.mp hz).1
    dsimp [Z]
    norm_num [ProfileCertificate.centerZ,ProfileCertificate.radius] at hl ⊢
    linarith
  have hH : regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ)) ≠ 0 := by
    exact (ProfileCertificate.disk_free_exterior w Z le_rfl).1
  have hD : deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6) (-Complex.I*(Z : ℂ))=0 := by
    change ProfileCertificate.freeProfileJ b Z=0 at hw
    rw [ProfileCertificate.freeProfileJ_eq_log_derivative b Z hZ] at hw
    exact neg_eq_zero.mp ((div_eq_zero_iff.mp hw).resolve_right hH)
  have hDisk : (b,Z) ∈ freeMatchingDisk := by
    have hn : ‖w.val‖ ≤ (ProfileCertificate.radius : ℝ) := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using w.property
    have hs := sq_le_sq₀ (norm_nonneg w.val) (by norm_num [ProfileCertificate.radius]) |>.2 hn
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply] at hs
    simpa [freeMatchingDisk,b,Z,ProfileCertificate.centerB,ProfileCertificate.centerZ,
      ProfileCertificate.radius,pow_two] using hs
  refine ⟨b,Z,hDisk,contDiff_freeRadialProfile b Z hZ hH hD,?_,?_,?_⟩
  · exact ite_eq_left (freeProfileRadius_pos hZ).le
  · intro r hr
    exact freeRadialProfile_nonzero_on_disk w r hr
  · intro ell
    exact free_outgoing_count hR ell b Z hDisk

end DefocusingNLS

end OAI
