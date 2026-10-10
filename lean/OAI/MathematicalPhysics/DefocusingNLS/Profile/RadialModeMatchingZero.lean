import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRegularMode
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchingIntersection

namespace OAI

/-! An actual nonzero radial mode makes the regular/outgoing matching
determinant vanish. Both span statements are derived from the mode data. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatched_mode_matching_zero (n N : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (hN : 7≤N) (eta : ℝ) (heta : 0≤eta)
    (lam : ℂ) (hhalf : -(1/32 : ℝ)≤lam.re)
    (u : RadialSpectralMode (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold) N
      (radialMatchedProfile n z) (eta : ℂ) lam)
    (R : ℝ) (hR : innerBoundaryRadius<R) (Rp Rm : ℝ → E₄)
    (hpc : ContDiff ℝ 2 (fun r => (Rp r).1.1) ∧ ContDiff ℝ 2 (fun r => (Rp r).2.1))
    (hmc : ContDiff ℝ 2 (fun r => (Rm r).1.1) ∧ ContDiff ℝ 2 (fun r => (Rm r).2.1))
    (hp : ∀ r ∈ Ioc 0 R, HasDerivAt Rp
      (spectralPhysicalCircularField
        (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam)
        (eta : ℂ) (n+radialInnerShootingThreshold) (radialMatchedEvenProfile n z r) r (Rp r)) r)
    (hm : ∀ r ∈ Ioc 0 R, HasDerivAt Rm
      (spectralPhysicalCircularField
        (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam)
        (eta : ℂ) (n+radialInnerShootingThreshold) (radialMatchedEvenProfile n z r) r (Rm r)) r)
    (hrank : LinearIndependent ℂ ![Rp R,Rm R])
    (Yp Ym : ℂ → ℝ → E₄)
    (hYp : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      (eta : ℂ) (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (1,0) Yp)
    (hYm : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      (eta : ℂ) (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (0,1) Ym) :
    spectralMatchingDeterminant (Rp R) (Rm R)
      (spectralPhysicalPair (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (Yp lam) R)
      (spectralPhysicalPair (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (Ym lam) R)=0 := by
  have hR0 : 0<R := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) hR
  obtain ⟨a,ha⟩ := homogeneous_matched_mode_regular_span n N z hX hz eta heta lam u
    R hR0 Rp Rm hpc hmc hp hm hrank
  obtain ⟨b,hb⟩ := homogeneous_matched_pair_canonical_span n z hX hz (eta : ℂ) N hN
    lam hhalf u.first u.second u.first_c2 u.second_c2 u.equation u.bounded
    u.first_top u.second_top Yp Ym hYp hYm R hR
  rw [spectralMatchingDeterminant_zero_iff]
  refine ⟨a.1,a.2,-b.1,-b.2,?_,?_⟩
  · have h := sub_eq_zero.mpr (ha.symm.trans hb)
    simpa only [neg_smul,sub_eq_add_neg,neg_add,add_assoc] using h
  · by_cases h1 : a.1=0
    · right; left
      intro h2
      have he : harmonicRadialState u.first u.second R=0 := by simpa [h1,h2] using ha
      exact homogeneous_matched_mode_state_ne_zero n N z hX hz (eta : ℂ) lam u R hR0 he
    · exact Or.inl h1

end DefocusingNLS

end OAI
