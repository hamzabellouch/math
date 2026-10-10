import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalOscillatoryEnergy

namespace OAI

/-! A good initial Cauchy point and bounded forcing give a uniform bound
for the oscillatory channel throughout the remaining shell. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralPhysicalLiouvillePair_oscillatory_bound
    (a beta eta : ℝ) (m : ℕ) (Q : ℝ → ℂ) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a beta m Q (eta : ℂ) lam f g)
    (hQ : ContinuousOn Q (Ioi 0)) (C R r₀ B A M : ℝ)
    (hbeta : 0 ≤ beta) (heta : 0 ≤ eta) (hw : 2 ≤ lam.im)
    (hgamma : |a+lam.re-3| ≤ 8) (hC : 0 ≤ C) (hR : 0 < R)
    (hRr : R ≤ r₀) (hrB : r₀ ≤ B) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hL : eta+99/4 ≤ C*lam.im) (hCR : 2*C ≤ R^2)
    (hinit : spectralOscillatoryEnergy
      (homogeneousSpectralLocalizationFrequency (-1) beta eta lam.im r₀)
      (spectralPhysicalLiouvillePair f g r₀).2 ≤ A)
    (hforce : (∫ r in r₀..B, ‖spectralShellMinusForcing m (Q r) r
      (spectralPhysicalLiouvillePair f g r)‖^2) ≤ M) :
    ∀ r ∈ Icc r₀ B,
      ‖(spectralPhysicalLiouvillePair f g r).2.2‖^2+
      lam.im*‖(spectralPhysicalLiouvillePair f g r).2.1‖^2 ≤
        2*(A+M)*Real.exp ((2/R+4*C/R^3+17)*(B-R)) := by
  have hb := spectralPhysicalLiouvillePair_oscillatory_energy a beta eta m Q lam f g hf hg he
    hQ C R r₀ B hbeta heta hw hgamma hC hR hRr hrB hL hCR
  let K := 2/R+4*C/R^3+17
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  intro r hr
  have he := hb r hr
  have hbase := add_le_add hinit hforce
  have hex : Real.exp (K*(r-r₀)) ≤ Real.exp (K*(B-R)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hr.2]) hK)
  have henergy : spectralOscillatoryEnergy
      (homogeneousSpectralLocalizationFrequency (-1) beta eta lam.im r)
      (spectralPhysicalLiouvillePair f g r).2 ≤ (A+M)*Real.exp (K*(B-R)) :=
    he.trans ((mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left hex (add_nonneg hA hM)))
  have hF := spectralNoTurn_frequency_lower beta eta lam.im C R r hbeta
    (by linarith) hR (hRr.trans hr.1) hL hCR
  simp only [spectralOscillatoryEnergy,← Complex.sq_norm] at henergy
  change _ ≤ 2*(A+M)*Real.exp (K*(B-R))
  nlinarith [sq_nonneg r,sq_nonneg ‖(spectralPhysicalLiouvillePair f g r).2.2‖,
    mul_nonneg (show 0 ≤ homogeneousSpectralLocalizationFrequency (-1) beta eta lam.im r-lam.im/2 by
      nlinarith [sq_nonneg r]) (sq_nonneg ‖(spectralPhysicalLiouvillePair f g r).2.1‖)]

end DefocusingNLS

end OAI
