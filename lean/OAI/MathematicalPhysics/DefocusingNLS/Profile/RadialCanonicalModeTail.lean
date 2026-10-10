import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingTail

namespace OAI

/-! A fixed outgoing representation starting at any chosen matching radius. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "V₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem homogeneous_matched_pair_canonical_tail_from
    (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (eta : ℂ) (N : ℕ) (hN : 7 ≤ N)
    (lam : ℂ) (hhalf : -(1 / 32 : ℝ) ≤ lam.re)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold)
      (radialMatchedProfile n z) eta lam f g)
    (hbounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖(f r, g r)‖ ≤ M)
    (hL2f : IntegrableOn (fun r => r ^ 11 * ‖iteratedDeriv N f r‖ ^ 2) (Ioi 0))
    (hL2g : IntegrableOn (fun r => r ^ 11 * ‖iteratedDeriv N g r‖ ^ 2) (Ioi 0))
    (Yp Ym : ℂ → ℝ → V₄)
    (hYp : IsCanonicalHolomorphicColumn (radialShootingNu (n + radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n + radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (1, 0) Yp)
    (hYm : IsCanonicalHolomorphicColumn (radialShootingNu (n + radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n + radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (0, 1) Ym)
    (R : ℝ) (hR : innerBoundaryRadius<R)
 :
    ∃ c : ℂ × ℂ, ∀ r, R ≤ r →
      harmonicRadialState f g r =
        c.1 • spectralPhysicalPair (radialShootingNu (n + radialInnerShootingThreshold) z - 2 * lam)
          (star (radialShootingNu (n + radialInnerShootingThreshold) z) - 2 * lam) (Yp lam) r +
        c.2 • spectralPhysicalPair (radialShootingNu (n + radialInnerShootingThreshold) z - 2 * lam)
          (star (radialShootingNu (n + radialInnerShootingThreshold) z) - 2 * lam) (Ym lam) r := by
  let R₀ := R
  have hi : innerBoundaryRadius < R₀ := hR
  have hR₀ : 0 < R₀ := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) hi
  obtain ⟨c, hc⟩ := homogeneous_matched_pair_canonical_span n z hX hz eta N hN lam hhalf
    f g hf hg he hbounded hL2f hL2g Yp Ym hYp hYm R₀ hi
  refine ⟨c, ?_⟩
  intro r hr
  let ν := radialShootingNu (n + radialInnerShootingThreshold) z
  have hν : -2 * (radialShootingA n : ℂ) +
      2 * Complex.I * (radialShootingB (profileMatchingParameter z) : ℂ) = ν :=
    (radialShootingNu_physical n z).symm
  have hνm : -2 * (radialShootingA n : ℂ) -
      2 * Complex.I * (radialShootingB (profileMatchingParameter z) : ℂ) = star ν := by
    rw [← hν]
    simp only [star_add, star_mul, star_neg, star_ofNat, Complex.star_def,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  apply homogeneousPhysicalOutgoingPlane_forward (ν - 2 * lam) (star ν - 2 * lam) eta
    (n + radialInnerShootingThreshold) (radialMatchedProfile n z)
    (harmonicRadialState f g) _ _ R₀ r hR₀ hr
  · exact (radialMatchedProfile_contDiffOn n z hX hz).continuousOn.mono
      (fun _ ht => hR₀.trans_le ht.1)
  · intro t ht
    simpa only [hν, hνm] using harmonicRadialState_hasDerivAt (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold)
      (radialMatchedProfile n z) f g eta lam hf hg he t (hR₀.trans_le ht.1)
  · exact fun t ht => homogeneous_matched_canonicalColumn_derivative n z eta lam (1, 0)
      Yp hYp t (hi.trans_le ht.1)
  · exact fun t ht => homogeneous_matched_canonicalColumn_derivative n z eta lam (0, 1)
      Ym hYm t (hi.trans_le ht.1)
  · exact hc

end DefocusingNLS

end OAI
