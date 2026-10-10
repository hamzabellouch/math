import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedEvenProfile
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralC1HarmonicMembership
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalGaugePair

namespace OAI

/-! Actual C1 physical channels give vectors in the weighted gauge energy space. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedGaugeJet (k : ℕ) (hk : 1 ≤ k) (n ell : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 < R)
    (F G : ℝ → ℂ) (hF : ContDiff ℝ k F) (hG : ContDiff ℝ k G) :
    ∃ f g : ℝ → ℂ, ContDiff ℝ k f ∧ ContDiff ℝ k g ∧
      ∃ u : SpectralHarmonicPair ell R,
      (∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.fst r=f r) ∧
      (∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.snd r=g r) ∧
      (spectralHarmonicDerivative ell R u.fst =ᵐ[radialPressureMeasure R] deriv f) ∧
      (spectralHarmonicDerivative ell R u.snd =ᵐ[radialPressureMeasure R] deriv g) ∧
      (∀ r, (radialMatchedEvenProfile n z r*(f r+Complex.I*g r),
        star (radialMatchedEvenProfile n z r)*(f r-Complex.I*g r))=(F r,G r)) ∧
      ∀ r ∈ Ioc 0 R,
      spectralPhysicalValueMap (spectralPhysicalGaugePair (radialMatchedProfile n z)
        (spectralHarmonicRepresentative ell R hR u.fst)
        (spectralHarmonicRepresentative ell R hR u.snd) r)=(F r,G r) := by
  let Q := radialMatchedEvenProfile n z
  have hQ : ContDiff ℝ k Q := (radialMatchedEvenProfile_contDiff n z hX hz).of_le (by simp)
  have hQn (r : ℝ) : Q r ≠ 0 := radialMatchedEvenProfile_ne_zero n z hX r
  have hQs : ContDiff ℝ k (fun r => star (Q r)) :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp hQ
  have hQsn (r : ℝ) : star (Q r) ≠ 0 := star_ne_zero.mpr (hQn r)
  let f := fun r => (1/2 : ℂ)*(F r/Q r+G r/star (Q r))
  let g := fun r => (1/(2*Complex.I) : ℂ)*(F r/Q r-G r/star (Q r))
  have hf : ContDiff ℝ k f := by
    dsimp only [f]
    simp only [div_eq_mul_inv]
    exact contDiff_const.mul
      ((hF.mul (hQ.inv hQn)).add (hG.mul (hQs.inv hQsn)))
  have hg : ContDiff ℝ k g := by
    dsimp only [g]
    simp only [div_eq_mul_inv]
    exact contDiff_const.mul
      ((hF.mul (hQ.inv hQn)).sub (hG.mul (hQs.inv hQsn)))
  have hinverse (r : ℝ) : (Q r*(f r+Complex.I*g r),
      star (Q r)*(f r-Complex.I*g r))=(F r,G r) := by
    dsimp only [f,g]
    apply Prod.ext <;> dsimp only <;> field_simp [hQn r,hQsn r,Complex.I_ne_zero] <;> ring
  obtain ⟨u,hu,hdu⟩ := spectralC1HarmonicJet ell R hR f (hf.of_le (by exact_mod_cast hk))
  obtain ⟨v,hv,hdv⟩ := spectralC1HarmonicJet ell R hR g (hg.of_le (by exact_mod_cast hk))
  let w : SpectralHarmonicPair ell R := WithLp.toLp 2 (u,v)
  refine ⟨f,g,hf,hg,w,hu,hv,hdu,hdv,hinverse,fun r hr => ?_⟩
  change spectralPhysicalValueMap (spectralPhysicalGaugePair (radialMatchedProfile n z)
    (spectralHarmonicRepresentative ell R hR u)
    (spectralHarmonicRepresentative ell R hR v) r)=(F r,G r)
  have he : Q r=radialMatchedProfile n z r := radialMatchedEvenProfile_nonneg n z r hr.1.le
  have hn : radialMatchedProfile n z r ≠ 0 := radialMatchedProfile_ne_zero n z hX r hr.1.le
  have hns : star (radialMatchedProfile n z r) ≠ 0 := star_ne_zero.mpr hn
  change (radialMatchedProfile n z r*(spectralHarmonicRepresentative ell R hR u r+
      Complex.I*spectralHarmonicRepresentative ell R hR v r),
    star (radialMatchedProfile n z r)*(spectralHarmonicRepresentative ell R hR u r-
      Complex.I*spectralHarmonicRepresentative ell R hR v r))=(F r,G r)
  rw [hu r hr,hv r hr]
  dsimp only [f,g]
  rw [he]
  apply Prod.ext <;> dsimp only <;> field_simp [hn,hns,Complex.I_ne_zero] <;> ring

theorem radialMatchedGaugeMembership (n ell : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 < R)
    (F G : ℝ → ℂ) (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) :
    ∃ u : SpectralHarmonicPair ell R, ∀ r ∈ Ioc 0 R,
      spectralPhysicalValueMap (spectralPhysicalGaugePair (radialMatchedProfile n z)
        (spectralHarmonicRepresentative ell R hR u.fst)
        (spectralHarmonicRepresentative ell R hR u.snd) r)=(F r,G r) := by
  obtain ⟨f,g,hf,hg,u,hu,hv,hdu,hdv,hpair,he⟩ :=
    radialMatchedGaugeJet 1 le_rfl n ell z hX hz R hR F G hF hG
  exact ⟨u,he⟩

end DefocusingNLS

end OAI
