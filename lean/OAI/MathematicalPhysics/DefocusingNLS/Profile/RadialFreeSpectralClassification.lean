import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeSimpleZeros

namespace OAI

/-! Exact free spectral classification at every matched limiting profile. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialFree_spectral_zero_iff (hR : RectangleRouche) (w : RadialShootingDisk)
    (hw : diskProfile w=0) (ell : ℕ) (lam : ℂ) (hhalf : -(1/32 : ℝ)≤lam.re) :
    spectralSlowDeterminant ell (radialShootingB w) ((radialShootingR w)^2/4) lam=0 ↔
      (ell=0 ∧ (lam=0 ∨ lam=1)) ∨ (ell=1 ∧ lam=1/2) := by
  by_cases h0 : ell=0
  · subst ell
    simpa only [true_and,zero_ne_one,false_and,or_false] using
      radialFree_phase_scaling_zeros hR w hw lam hhalf
  by_cases h1 : ell=1
  · subst ell
    simpa only [one_ne_zero,false_and,true_and,false_or] using
      radialFree_translation_zero hR w hw lam hhalf
  have hn := free_outgoing_nonzero hR ell (by omega) _ _
    (radialShooting_freeMatchingDisk w) lam hhalf
  simp only [h0,h1,false_and,false_or,hn,iff_self]

theorem radialFree_spectral_order (hR : RectangleRouche) (w : RadialShootingDisk)
    (hw : diskProfile w=0) (ell : ℕ) (lam : ℂ) (hhalf : -(1/32 : ℝ)≤lam.re) :
    analyticOrderAt (spectralSlowDeterminant ell (radialShootingB w)
      ((radialShootingR w)^2/4)) lam =
      if (ell=0 ∧ (lam=0 ∨ lam=1)) ∨ (ell=1 ∧ lam=1/2) then 1 else 0 := by
  classical
  by_cases h : (ell=0 ∧ (lam=0 ∨ lam=1)) ∨ (ell=1 ∧ lam=1/2)
  · rw [ite_eq_left h]
    obtain ⟨hp,ht,hs⟩ := radialFree_symmetry_zeros_simple hR w hw
    rcases h with ⟨rfl,rfl | rfl⟩ | ⟨rfl,rfl⟩
    · exact hp
    · exact hs
    · exact ht
  · rw [ite_eq_right h]
    exact analyticOrderAt_eq_zero.mpr (Or.inr
      (fun hz => h ((radialFree_spectral_zero_iff hR w hw ell lam hhalf).mp hz)))

end DefocusingNLS

end OAI
