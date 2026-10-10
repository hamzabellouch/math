import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseIIGoodPoint
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedForcingEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalOscillatoryBound

namespace OAI

/-! The actual normalized Case II eigenpair has a uniformly bounded
negative-channel Cauchy energy from its first-half good point onward. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_caseII_oscillatory_bound
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall)
    (z0 : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z0))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hmatch : ∀ i, radialMatchingMap (s i) (z i) = 0)
    (N : ℕ) (hN : 7 ≤ N) (lam : ℕ → ℂ) (ell : ℕ → ℕ)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (lam i).re) (hupper : ∀ i, (lam i).re ≤ 4)
    (hw : Tendsto (fun i => (lam i).im) atTop atTop)
    (C R B : ℝ) (hC : 0 ≤ C) (hR : innerBoundaryRadius < R) (hRB : R < B) (hCR : 2*C ≤ R^2)
    (hangular : ∀ᶠ i in atTop, (ell i : ℝ)*(ell i+10)+99/4 ≤ C*(lam i).im)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (he : ∀ i, IsHarmonicRadialEigenpair (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i)) (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i) (f i) (g i))
    (hbounded : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖(f i r,g i r)‖ ≤ M)
    (hL2f : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (f i) r‖^2) (Ioi 0))
    (hL2g : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (g i) r‖^2) (Ioi 0))
    (hnorm : ∀ i, (∫ r in R..B, spectralPhysicalShellDensity (f i) (g i) r) ≤ 1) :
    ∃ (φ : ℕ → ℕ) (M : ℝ), StrictMono φ ∧ 0 ≤ M ∧ ∀ᶠ n in atTop,
      ∃ r₀ ∈ Icc R ((R+B)/2),
      (lam (φ n)).im*‖(spectralPhysicalLiouvillePair (f (φ n)) (g (φ n)) r₀).1.1‖^2 ≤ M ∧
      ∀ r ∈ Icc r₀ B,
        let q := spectralPhysicalLiouvillePair (f (φ n)) (g (φ n)) r
        ‖q.2.2‖^2+(lam (φ n)).im*‖q.2.1‖^2 ≤ M := by
  obtain ⟨φ,hφ,hpoint⟩ := spectralMatched_caseII_good_point s hs z z0 hz hX hmatch N hN lam ell
    hhalf hupper hw C R B hC hR hRB hCR hangular f g hf hg he hbounded hL2f hL2g hnorm
  have hR0 : 0 < R := by linarith [innerBoundaryRadius_bounds.1]
  let G := 2*(1+(11/(2*R)+B/4)^2)/((R+B)/2-R)
  let D := C/R^2+2
  let A := G+8*48^2*D*G
  let M₀ := 2*(A+(1/R^2)^2)*Real.exp ((2/R+4*C/R^3+17)*(B-R))
  let M := max (8*48^2*G) M₀
  have hwidth : 0 < (R+B)/2-R := by linarith
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hM₀ : 0 ≤ M₀ := by dsimp only [M₀]; positivity
  have hM : 0 ≤ M := hM₀.trans (le_max_right _ _)
  have hforce := (hs.comp hφ).tendsto_atTop.eventually (radialMatched_shell_forcing_energy R B hR hRB.le)
  refine ⟨φ,M,hφ,hM,?_⟩
  filter_upwards [hpoint,hforce,hφ.tendsto_atTop.eventually hangular,
    (hw.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop (2*(B^2/16+1)))]
    with n hpn hfn han hwn
  obtain ⟨r₀,hr₀,hqderiv,hqvalue⟩ := hpn
  dsimp only [Function.comp_def] at hwn hfn
  let q := spectralPhysicalLiouvillePair (f (φ n)) (g (φ n))
  have hw2 : 2 ≤ (lam (φ n)).im := by nlinarith [sq_nonneg B]
  have hbeta := (radialShooting_geometry (profileMatchingParameter (z (φ n)))).1
  have hbeta0 : 0 ≤ radialShootingB (profileMatchingParameter (z (φ n))) := by linarith [hbeta.1]
  have hbeta1 : radialShootingB (profileMatchingParameter (z (φ n))) ≤ 1 := by linarith [hbeta.2]
  have hgamma : |radialShootingA (s (φ n))+(lam (φ n)).re-3| ≤ 8 := by
    have ha := radialShootingA_bounds (s (φ n)) (profileMatchingParameter (z (φ n)))
    exact abs_le.mpr ⟨by linarith [hhalf (φ n)],by linarith [hupper (φ n)]⟩
  have hrB : r₀ ≤ B := by linarith [hr₀.2]
  have hfreq := spectralCaseII_shell_frequency
    (radialShootingB (profileMatchingParameter (z (φ n)))) ((ell (φ n) : ℝ)*(ell (φ n)+10))
    (lam (φ n)).im C R B r₀ hbeta0 hbeta1 (by positivity) hC hR0 hr₀.1 hrB hwn han hCR
  have hv : (lam (φ n)).im*‖(q r₀).2.1‖^2 ≤ 8*48^2*G := by
    have hw0 : 0 ≤ (lam (φ n)).im := by linarith
    have hsquare : (Real.sqrt (lam (φ n)).im/48)^2 = (lam (φ n)).im/48^2 := by
      rw [div_pow,Real.sq_sqrt hw0]
    rw [hsquare] at hqvalue
    change (lam (φ n)).im/48^2*(‖(q r₀).1.1‖^2+‖(q r₀).2.1‖^2) ≤ 8*G at hqvalue
    nlinarith [mul_nonneg hw0 (sq_nonneg ‖(q r₀).1.1‖)]
  have hi : spectralOscillatoryEnergy
      (homogeneousSpectralLocalizationFrequency (-1) (radialShootingB (profileMatchingParameter (z (φ n))))
        ((ell (φ n) : ℝ)*(ell (φ n)+10)) (lam (φ n)).im r₀) (q r₀).2 ≤ A := by
    have hdv : ‖(q r₀).2.2‖^2 ≤ G := by
      change ‖(q r₀).1.2‖^2+‖(q r₀).2.2‖^2 ≤ G at hqderiv
      nlinarith [sq_nonneg ‖(q r₀).1.2‖]
    have hFup := (le_abs_self _).trans hfreq.2.2.2
    change _ ≤ D*(lam (φ n)).im at hFup
    have hprod := mul_le_mul_of_nonneg_right hFup (sq_nonneg ‖(q r₀).2.1‖)
    have hprod' := mul_le_mul_of_nonneg_left hv hD
    dsimp only [spectralOscillatoryEnergy,A]
    simp only [← Complex.sq_norm]
    nlinarith only [hdv,hprod,hprod']
  have hQ : ContinuousOn (radialMatchedProfile (s (φ n)) (z (φ n))) (Ioi 0) :=
    (radialMatchedProfile_contDiffOn _ _ (hX (φ n)) (hmatch (φ n))).continuousOn
  have hfbound := hfn (z (φ n)) (hX (φ n)) (hmatch (φ n)) (f (φ n)) (g (φ n))
    (hf (φ n)) (hg (φ n)) 1 (hnorm (φ n)) r₀ ⟨hr₀.1,hrB⟩
  simp only [mul_one] at hfbound
  have hosc := spectralPhysicalLiouvillePair_oscillatory_bound
    (radialShootingA (s (φ n))) (radialShootingB (profileMatchingParameter (z (φ n))))
    ((ell (φ n) : ℝ)*(ell (φ n)+10)) (s (φ n)+radialInnerShootingThreshold)
    (radialMatchedProfile (s (φ n)) (z (φ n))) (lam (φ n)) (f (φ n)) (g (φ n))
    (hf (φ n)) (hg (φ n)) (he (φ n)) hQ C R r₀ B A ((1/R^2)^2)
    hbeta0 (by positivity) hw2 hgamma hC hR0 hr₀.1 hrB hA (sq_nonneg _) han hCR hi hfbound
  refine ⟨r₀,hr₀,?_,?_⟩
  · apply le_trans _ (le_max_left _ _)
    have hw0 : 0 ≤ (lam (φ n)).im := by linarith
    rw [div_pow,Real.sq_sqrt hw0] at hqvalue
    change (lam (φ n)).im/48^2*(‖(q r₀).1.1‖^2+‖(q r₀).2.1‖^2) ≤ 8*G at hqvalue
    nlinarith [mul_nonneg hw0 (sq_nonneg ‖(q r₀).2.1‖)]
  · intro r hr
    exact (hosc r hr).trans (le_max_right _ _)

end DefocusingNLS

end OAI
