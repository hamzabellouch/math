import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialStripClassification
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralConjugation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralUpper

namespace OAI

/-! Exact conditional classification of all regular outgoing radial modes
in the counting half-plane, uniformly in every angular degree. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedSpectralMode_classification (hRou : RectangleRouche)
    (N : ℕ) (hN : 7 ≤ N) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ ell : ℕ, ∀ lam : ℂ, -(1/32 : ℝ) ≤ lam.re →
      Nonempty (RadialSpectralMode (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold) N
        (radialMatchedProfile n z) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam) →
      (ell=0 ∧ (lam=0 ∨ lam=1)) ∨ (ell=1 ∧ lam=1/2) := by
  filter_upwards [radialMatchedSpectralMode_strip_classification hRou N hN,
    radialMatchedSpectralMode_re_lt_four] with n hn hu z hX hz ell lam hl hmode
  obtain ⟨u⟩ := hmode
  have heq : (((ell : ℝ)*(ell+10) : ℝ) : ℂ)=(ell : ℂ)*(ell+10) := by push_cast; rfl
  have hlu : lam.re < 4 := hu z hX hz ell N hN lam (by simpa only [heq] using u)
  by_cases hi : 0 ≤ lam.im
  · exact hn z hX hz ell lam hl hlu.le hi ⟨u⟩
  · have hci : 0 ≤ (star lam).im := by simpa only [Complex.star_def,Complex.conj_im] using neg_nonneg.mpr (le_of_not_ge hi)
    have hc := hn z hX hz ell (star lam) (by simpa using hl) (by simpa using hlu.le) hci ⟨u.conjugate⟩
    rcases hc with ⟨he,hv | hv⟩ | ⟨he,hv⟩
    · exact Or.inl ⟨he,Or.inl (by simpa using congrArg star hv)⟩
    · exact Or.inl ⟨he,Or.inr (by simpa using congrArg star hv)⟩
    · exact Or.inr ⟨he,by simpa using congrArg star hv⟩

end DefocusingNLS

end OAI
