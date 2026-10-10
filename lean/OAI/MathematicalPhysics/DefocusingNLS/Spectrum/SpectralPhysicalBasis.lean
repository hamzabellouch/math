import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingBasis
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalProfile
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalRank
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalAnalytic

namespace OAI

/-! A holomorphic rank-two family solving the actual physical exterior spectral system. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem canonical_physical_outgoing_basis (m : ℕ) (hm : 1 ≤ m)
    (b : ℝ) (c : ℂ) (hc : c ≠ 0) (η : ℂ) (L : ℝ)
    (hX : HasRadialExterior (-1/(m : ℂ)+2*Complex.I*(b : ℂ)) m c L) :
    let μ := -1/(m : ℂ)+2*Complex.I*(b : ℂ)
    let Q := fun r => Complex.exp (μ*(Real.log r : ℂ))*
      (radialExteriorCanonical μ m c L (Real.log r)).1
    ∃ Vp Vm : ℂ → ℝ → E₄,
      (∀ lam r, 1 ≤ r → HasDerivAt (Vp lam)
        (spectralPhysicalCircularField (μ-2*lam) (star μ-2*lam) η m (Q r) r (Vp lam r)) r) ∧
      (∀ lam r, 1 ≤ r → HasDerivAt (Vm lam)
        (spectralPhysicalCircularField (μ-2*lam) (star μ-2*lam) η m (Q r) r (Vm lam r)) r) ∧
      (∀ lam r, 1 ≤ r → LinearIndependent ℂ ![Vp lam r,Vm lam r]) ∧
      (∀ z r, 1 ≤ r → AnalyticAt ℂ (fun lam => Vp lam r) z ∧
        AnalyticAt ℂ (fun lam => Vm lam r) z) := by
  intro μ Q
  obtain ⟨Yp,Ym,hp,hm',_hplim,_hmlim,hrank,ha⟩ :=
    canonical_holomorphic_circular_basis μ μ (star μ) η c m hm L hX hc
  let Vp := fun lam => spectralPhysicalPair (μ-2*lam) (star μ-2*lam) (Yp lam)
  let Vm := fun lam => spectralPhysicalPair (μ-2*lam) (star μ-2*lam) (Ym lam)
  have hscale (r : ℝ) (hr : 0 < r) :
      (Complex.exp (μ*(Real.log r : ℂ))*star (Complex.exp (μ*(Real.log r : ℂ))))^m=
        1/(r : ℂ)^2 := spectralPhysicalFactor_scale m (by omega) b r hr
  refine ⟨Vp,Vm,?_,?_,?_,?_⟩
  · intro lam r hr
    exact spectralPhysicalPair_hasDerivAt μ lam η m hm
      (fun t => (radialExteriorCanonical μ m c L t).1) (Yp lam) r
      (zero_lt_one.trans_le hr) (hscale r (zero_lt_one.trans_le hr))
      (hp lam (Real.log r) (Real.log_nonneg hr))
  · intro lam r hr
    exact spectralPhysicalPair_hasDerivAt μ lam η m hm
      (fun t => (radialExteriorCanonical μ m c L t).1) (Ym lam) r
      (zero_lt_one.trans_le hr) (hscale r (zero_lt_one.trans_le hr))
      (hm' lam (Real.log r) (Real.log_nonneg hr))
  · intro lam r hr
    exact spectralPhysicalPair_rank (μ-2*lam) (star μ-2*lam) (Yp lam) (Ym lam) r
      (zero_lt_one.trans_le hr).ne' (hrank lam (Real.log r) (Real.log_nonneg hr))
  · intro z r hr
    have hνp : AnalyticAt ℂ (fun lam : ℂ => μ-2*lam) z :=
      analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
    have hνm : AnalyticAt ℂ (fun lam : ℂ => star μ-2*lam) z :=
      analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
    exact ⟨spectralPhysicalPair_analyticAt _ _ Yp z r hνp hνm
        (ha z (Real.log r) (Real.log_nonneg hr)).1,
      spectralPhysicalPair_analyticAt _ _ Ym z r hνp hνm
        (ha z (Real.log r) (Real.log_nonneg hr)).2⟩

end DefocusingNLS

end OAI
