import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalExclusion
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralMode
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMatchedOutgoing

namespace OAI

/-! Every finite limit of actual fixed-harmonic eigenvalues is a zero of the
certified free outgoing determinant. No outgoing premise is assumed. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedSpectralMode_limit_zero
    (ell N : ℕ) (hN : 7 ≤ N) (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (hz₁ : z₀.val.1=0) (hz₀ : diskProfile (profileMatchingParameter z₀)=0)
    (lam : ℕ → ℂ) (lam₀ : ℂ) (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hlam₀ : -(1/32 : ℝ)≤lam₀.re) (hhalf : ∀ i, -(1/32 : ℝ)≤(lam i).re)
    (mode : ∀ i, RadialSpectralMode (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold) N
      (radialMatchedProfile (s i) (z i)) ((ell : ℂ)*(ell+10)) (lam i)) :
    spectralSlowDeterminant ell (radialShootingB (profileMatchingParameter z₀))
      ((radialShootingR (profileMatchingParameter z₀))^2/4) lam₀=0 := by
  by_contra hD
  obtain ⟨R,_hR0,hR,Y,Z,hYZ,hno⟩ := radialMatchedCanonical_exclusion_with_det
    ell s hs z z₀ hz hX hm hz₁ hz₀ lam lam₀ hlam hlam₀ hD 0
  obtain ⟨i,hi,hYi⟩ := (hno.and hYZ).exists
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] at hYi
  let u := mode i
  have hη : (((ell : ℝ)*(ell+10) : ℝ) : ℂ)=(ell : ℂ)*(ell+10) := by push_cast; rfl
  have he : IsHarmonicRadialEigenpair (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i)) (((ell : ℝ)*(ell+10) : ℝ) : ℂ)
      (lam i) u.first u.second := by
    rw [hη]
    exact u.equation
  have hb := homogeneous_matched_pair_canonical_robin
    (s i) (z i) (hX i) (hm i) ((ell : ℂ)*(ell+10)) N hN (lam i) (hhalf i)
    u.first u.second u.first_c2 u.second_c2 u.equation u.bounded u.first_top u.second_top
    (Y i) (Z i) hYi.1 hYi.2 R hR hi.1
  have hzpair := hi.2 u.first u.second u.first_c2 u.second_c2 he hb
  obtain ⟨r,hr,hrn⟩ := harmonicRadialEigenpair_nonzero_on_ball _ _ _ _ u.first u.second _ _
    (radialMatchedProfile_differentiable (s i) (z i) (hX i) (hm i)).continuous.continuousOn
    u.first_c2 u.second_c2 u.equation u.nonzero R
    (((by norm_num : (0 : ℝ)<1).trans_le innerBoundaryRadius_bounds.1).trans hR)
  obtain ⟨hf,hg⟩ := hzpair r hr
  rcases hrn with hrn | hrn
  · exact hrn hf
  · exact hrn hg

end DefocusingNLS

end OAI
