import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularPhysicalBasis
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalBasis
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialProfileSplice

namespace OAI

/-! Interior and outgoing bases for the same actually matched stationary profile. -/

open Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatched_spectral_bases (n ell : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R L : ℝ) (hR : innerBoundaryRadius < R) (hL : 0 ≤ L) :
    let m := n+radialInnerShootingThreshold
    let μ := radialShootingNu m z
    let Q := radialMatchedProfile n z
    let F := fun lam r => spectralPhysicalCircularField (μ-2*lam) (star μ-2*lam)
      ((ell*(ell+10) : ℕ) : ℂ) m (Q r) r
    ∃ Rp Rm Op Om : ℂ → ℝ → E₄,
      (∀ lam, ‖lam‖ ≤ L → ∀ r ∈ Ioc 0 R, HasDerivAt (Rp lam) (F lam r (Rp lam r)) r) ∧
      (∀ lam, ‖lam‖ ≤ L → ∀ r ∈ Ioc 0 R, HasDerivAt (Rm lam) (F lam r (Rm lam r)) r) ∧
      (∀ lam r, R ≤ r → HasDerivAt (Op lam) (F lam r (Op lam r)) r) ∧
      (∀ lam r, R ≤ r → HasDerivAt (Om lam) (F lam r (Om lam r)) r) ∧
      (∀ lam, ‖lam‖ ≤ L → LinearIndependent ℂ ![Rp lam R,Rm lam R]) ∧
      (∀ lam, LinearIndependent ℂ ![Op lam R,Om lam R]) ∧
      (∀ w, ‖w‖ ≤ L → AnalyticAt ℂ (fun lam => Rp lam R) w ∧
        AnalyticAt ℂ (fun lam => Rm lam R) w ∧
        AnalyticAt ℂ (fun lam => Op lam R) w ∧ AnalyticAt ℂ (fun lam => Om lam R) w) ∧
      (∃ Wp Wm : ℂ → ℝ → E₄,
        (∀ lam, Continuous (Wp lam) ∧ Continuous (Wm lam) ∧
          Wp lam 0=((1,0),(0,0)) ∧ Wm lam 0=((0,0),(1,0))) ∧
        (∀ lam r, Rp lam r=spectralAngularPair ell (Wp lam) r ∧
          Rm lam r=spectralAngularPair ell (Wm lam) r)) := by
  intro m μ Q F
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one (innerBoundaryRadius_bounds.1.trans hR.le)
  have hR1 : 1 ≤ R := innerBoundaryRadius_bounds.1.trans hR.le
  obtain ⟨Rp,Rm,hRp,hRm,hrank,ha,hnorm⟩ :=
    exists_regular_physical_basis_normalized ell m μ (star μ) R L hR0 hL Q
      (radialMatchedProfile_differentiable n z hX hz).continuous
  have hm : 1 ≤ m := radialShootingInner_power_pos n (profileMatchingParameter z)
  have hμ : radialShootingNu m z=
      -1/(m : ℂ)+2*Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ) := by
    unfold radialShootingNu radialShootingQ
    ring
  let Qout := fun r => Complex.exp (μ*(Real.log r : ℂ))*
    (radialExteriorCanonical μ m (radialShootingM z) (Real.log innerBoundaryRadius) (Real.log r)).1
  have hX' : HasRadialExterior
      (-1/(m : ℂ)+2*Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ))
      m (radialShootingM z) (Real.log innerBoundaryRadius) := by
    rw [← hμ]
    exact hX
  obtain ⟨Op,Om,hOp,hOm,horank,hoa⟩ := canonical_physical_outgoing_basis m hm
    (radialShootingB (profileMatchingParameter z)) (radialShootingM z)
    (radialShootingM_ne_zero z) ((ell*(ell+10) : ℕ) : ℂ) (Real.log innerBoundaryRadius) hX'
  have hQout (r : ℝ) (hr : R ≤ r) : Q r=Qout r := by
    change radialMatchedProfile n z r=Qout r
    rw [radialMatchedProfile,ite_eq_right (not_le.mpr (hR.trans_le hr))]
    rfl
  refine ⟨Rp,Rm,Op,Om,hRp,hRm,?_,?_,hrank,?_,?_,hnorm⟩
  · intro lam r hr
    have he := hOp lam r (hR1.trans hr)
    rw [← hμ] at he
    change HasDerivAt (Op lam)
      (spectralPhysicalCircularField (μ-2*lam) (star μ-2*lam)
        ((ell*(ell+10) : ℕ) : ℂ) m (Qout r) r (Op lam r)) r at he
    simpa only [F,hQout r hr] using he
  · intro lam r hr
    have he := hOm lam r (hR1.trans hr)
    rw [← hμ] at he
    change HasDerivAt (Om lam)
      (spectralPhysicalCircularField (μ-2*lam) (star μ-2*lam)
        ((ell*(ell+10) : ℕ) : ℂ) m (Qout r) r (Om lam r)) r at he
    simpa only [F,hQout r hr] using he
  · intro lam
    exact horank lam R hR1
  · intro w hw
    exact ⟨(ha w hw R hR0.le).1,(ha w hw R hR0.le).2,(hoa w R hR1).1,(hoa w R hR1).2⟩

end DefocusingNLS

end OAI
