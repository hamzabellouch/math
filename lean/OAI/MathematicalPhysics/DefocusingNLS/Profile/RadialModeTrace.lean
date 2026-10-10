import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialModeLine

namespace OAI

/-! # One nonzero scalar trace separates a radial mode line -/

namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialModeTrace {a b : ℝ} {m N : ℕ} {Q : ℝ → ℂ} {η lam : ℂ}
    (u : RadialSpectralMode a b m N Q η lam) (first : Bool) (r : ℝ) : ℂ :=
  if first then u.first r else u.second r

theorem radialModeTrace_exists {a b : ℝ} {m N : ℕ} {Q : ℝ → ℂ} {η lam : ℂ}
    (u : RadialSpectralMode a b m N Q η lam) :
    ∃ first : Bool, ∃ r : ℝ, 0 < r ∧ radialModeTrace u first r ≠ 0 := by
  obtain ⟨r, hr, h | h⟩ := u.nonzero
  · exact ⟨true, r, hr, h⟩
  · exact ⟨false, r, hr, h⟩

theorem RadialModeLine.trace_ne_zero {n ell N : ℕ} {z : ProfileMatchingBall} {lam : ℂ}
    (h : RadialModeLine n z ell N lam)
    (u v : RadialSpectralMode (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n + radialInnerShootingThreshold) N (radialMatchedProfile n z) ((ell : ℂ) * (ell + 10)) lam)
    (first : Bool) (r : ℝ) (hr : 0 < r) (hu : radialModeTrace u first r ≠ 0) :
    radialModeTrace v first r ≠ 0 := by
  obtain ⟨c, hc⟩ := h u v
  have hv : radialModeTrace v first r = c * radialModeTrace u first r := by
    cases first
    · exact (hc r hr).2
    · exact (hc r hr).1
  intro hz
  have hcz : c = 0 := (mul_eq_zero.mp (hv.symm.trans hz)).resolve_right hu
  obtain ⟨t, ht, hf | hg⟩ := v.nonzero
  · exact hf (by rw [(hc t ht).1, hcz, zero_mul])
  · exact hg (by rw [(hc t ht).2, hcz, zero_mul])

end DefocusingNLS

end OAI
