import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGluedMode
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchingData
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralColumnRank
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalRank

namespace OAI

/-! A zero of the actual matching determinant supplies a bounded classical mode. -/

open Set
open scoped ContDiff BoundedContinuousFunction
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem homogeneousGlued_matching_mode {n ell : ℕ} {z : ProfileMatchingBall} {R L : ℝ}
    (d : RadialMatchingData n z ell R L)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (N : ℕ) (hN : 7 ≤ N)
    (lam : ℂ) (hlam : ‖lam‖ ≤ L) (hhalf : -radialShootingA n ≤ lam.re)
    (hzero : d.determinant lam = 0) :
    Nonempty (RadialSpectralMode (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold) N
      (radialMatchedProfile n z) ((ell * (ell + 10) : ℕ) : ℂ) lam) := by
  let m := n + radialInnerShootingThreshold
  let ν := radialShootingNu m z
  let eta : ℂ := ((ell * (ell + 10) : ℕ) : ℂ)
  let Q := radialMatchedEvenProfile n z
  let Op := spectralPhysicalPair (ν - 2 * lam) (star ν - 2 * lam) (d.outgoingPlus lam)
  let Om := spectralPhysicalPair (ν - 2 * lam) (star ν - 2 * lam) (d.outgoingMinus lam)
  have hR : 0 < R := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) d.radius_gt
  have hR1 : 1 ≤ R := innerBoundaryRadius_bounds.1.trans d.radius_gt.le
  have hm : 1 ≤ m := radialShootingInner_power_pos n (profileMatchingParameter z)
  have hQc : ContDiff ℝ ∞ Q := radialMatchedEvenProfile_contDiff n z hX hz
  have hOp : ∀ r, R ≤ r → HasDerivAt Op
      (spectralPhysicalCircularField (ν - 2 * lam) (star ν - 2 * lam) eta m
        (Q r) r (Op r)) r := by
    intro r hr
    have hh := homogeneous_matched_canonicalColumn_derivative n z eta lam (1, 0)
      d.outgoingPlus d.plus_canonical r (d.radius_gt.trans_le hr)
    simpa only [Q, radialMatchedEvenProfile_nonneg n z r (hR.le.trans hr)] using hh
  have hOm : ∀ r, R ≤ r → HasDerivAt Om
      (spectralPhysicalCircularField (ν - 2 * lam) (star ν - 2 * lam) eta m
        (Q r) r (Om r)) r := by
    intro r hr
    have hh := homogeneous_matched_canonicalColumn_derivative n z eta lam (0, 1)
      d.outgoingMinus d.minus_canonical r (d.radius_gt.trans_le hr)
    simpa only [Q, radialMatchedEvenProfile_nonneg n z r (hR.le.trans hr)] using hh
  obtain ⟨q, hq, _⟩ := canonical_circular_expansion_data ν (radialShootingM z) m
    (Real.log innerBoundaryRadius) hX (radialShootingM_ne_zero z)
  have hrank : LinearIndependent ℂ ![Op R, Om R] := by
    apply spectralPhysicalPair_rank (ν - 2 * lam) (star ν - 2 * lam)
      (d.outgoingPlus lam) (d.outgoingMinus lam) R hR.ne'
    apply circular_columns_at_linearIndependent (ν - 2 * lam) (star ν - 2 * lam) eta m hm
      ‖q‖ (fun t => (radialExteriorCanonical ν m (radialShootingM z)
        (Real.log innerBoundaryRadius) t).1)
      (d.outgoingPlus lam) (d.outgoingMinus lam) _
      (d.plus_canonical.1 lam) (d.minus_canonical.1 lam)
      (d.plus_canonical.2.1 lam) (d.minus_canonical.2.1 lam)
      (Real.log R) (Real.log_nonneg hR1)
    intro t ht
    rw [← hq t ht]
    exact q.norm_coe_le_norm t
  obtain ⟨U, _a, _b, c, e, _hi, ho, hne, hfc, hgc, _hs, hU⟩ :=
    homogeneousGlued_matching_state (ν - 2 * lam) (star ν - 2 * lam) eta m Q
      hQc.contDiffOn R hR (d.regularPlus lam) (d.regularMinus lam) Op Om
      ⟨(d.regular_c2 lam).1, (d.regular_c2 lam).2.1⟩
      ⟨(d.regular_c2 lam).2.2.1, (d.regular_c2 lam).2.2.2⟩
      (d.plus_equation lam hlam) (d.minus_equation lam hlam) hOp hOm
      (d.regular_rank lam hlam) hrank hzero
  obtain ⟨u⟩ := homogeneousGlued_canonical_mode (radialShootingA n)
    (radialShootingB (profileMatchingParameter z)) ell m N hN ν (radialShootingM z)
    lam (radialShootingNu_physical n z) hhalf (Real.log innerBoundaryRadius) hX
    Q hQc U ⟨hfc, hgc⟩ hU R hR hne d.outgoingPlus d.outgoingMinus
    d.plus_canonical d.minus_canonical c e ho
  refine ⟨⟨u.first, u.second, u.first_c2, u.second_c2, ?_, u.first_smooth,
    u.second_smooth, u.first_top, u.second_top, u.bounded, u.nonzero⟩⟩
  intro r hr
  simpa only [Q, radialMatchedEvenProfile_nonneg n z r hr.le] using u.equation r hr

end DefocusingNLS

end OAI
