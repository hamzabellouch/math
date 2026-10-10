import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoupledBoundarySystem
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellForcingContinuity

namespace OAI

/-! The actual odd-power profile supplies all forcing estimates in the
coupled shell absorption argument. Only the scalar comparison data and the
remote outgoing condition remain at this interface. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_shell_boundary_absorb (C : ℝ) (hC : 0 < C) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius)) →
      (hz : radialMatchingMap n z = 0) →
      ∀ R E A kap B L : ℝ, innerBoundaryRadius < R → R ≤ E → 0 < kap →
      0 ≤ A → 0 ≤ B → (A+1)*(B/E+C/R)/kap^2 ≤ 1/2 →
      ∀ Sp Sm : SpectralScalarBoundarySystem R E A,
      (∀ t ∈ Icc R E, kap ≤ Sp.k t) → (∀ t ∈ Icc R E, kap ≤ Sm.k t) →
      ∀ q : ℝ → (ℂ × ℂ) × (ℂ × ℂ), ContinuousOn q (Icc R E) →
      (∀ t ∈ Icc R E, HasDerivAt (fun s => (q s).1)
        (spectralScalarField (Sp.V t) (q t).1+
          (0,spectralShellPlusForcing (n+radialInnerShootingThreshold)
            (radialMatchedProfile n z t) t (q t))) t) →
      (∀ t ∈ Icc R E, HasDerivAt (fun s => (q s).2)
        (spectralScalarField (Sm.V t) (q t).2+
          (0,spectralShellMinusForcing (n+radialInnerShootingThreshold)
            (radialMatchedProfile n z t) t (q t))) t) →
      max ‖(q E).1.2-Sp.beta*(q E).1.1‖ ‖(q E).2.2-Sm.beta*(q E).2.1‖ ≤
        B/E*max ‖(q E).1.1‖ ‖(q E).2.1‖ →
      (∀ r ∈ Icc R E, spectralShellPairNorm (Sp.k r) (Sm.k r)
        (Sp.extension (q R).1.1 r,Sm.extension (q R).2.1 r) ≤ L) →
      ∀ r ∈ Icc R E,
        spectralShellPairNorm (Sp.k r) (Sm.k r) (q r) ≤ 2*L ∧
        spectralShellPairNorm (Sp.k r) (Sm.k r)
          (q r-(Sp.extension (q R).1.1 r,Sm.extension (q R).2.1 r)) ≤
            2*((A+1)*(B/E+C/R)/kap^2)*L := by
  filter_upwards [radialMatched_shell_forcing_bound C hC] with n hn
  intro z hX hz R E A kap B L hRb hRE hkap hA hB hsmall Sp Sm hkp hkm q hq hqp hqm hremote hext
  have hR : 0 < R := by linarith [innerBoundaryRadius_bounds.1]
  have hQ : ContinuousOn (radialMatchedProfile n z) (Icc R E) :=
    (radialMatchedProfile_contDiffOn n z hX hz).continuousOn.mono
      (fun t ht => hR.trans_le ht.1)
  have hfc := spectralShellForcing_continuousOn (n+radialInnerShootingThreshold) R E hR
    (radialMatchedProfile n z) q hQ hq
  exact spectralCoupled_boundary_absorb Sp Sm kap C B L hR hRE hkap hA hC.le hB hsmall
    hkp hkm q _ _ hq hfc.1 hfc.2 hqp hqm
    (fun t ht => (hn z t (Sp.k t) (Sm.k t) kap (hRb.trans_le ht.1)
      hkap (hkp t ht) (hkm t ht) (q t)).1)
    (fun t ht => (hn z t (Sp.k t) (Sm.k t) kap (hRb.trans_le ht.1)
      hkap (hkp t ht) (hkm t ht) (q t)).2) hremote hext

end DefocusingNLS

end OAI
