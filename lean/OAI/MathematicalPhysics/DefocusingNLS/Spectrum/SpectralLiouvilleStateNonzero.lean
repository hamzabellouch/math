import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalLiouvillePair
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HarmonicRadialNonvanishing

namespace OAI

/-! The positive-radius Liouville transform preserves nonzero Cauchy
states of actual regular harmonic eigenpairs. -/

open Set
namespace DefocusingNLS

theorem spectralPhysicalLiouvillePair_state_zero (f g : ℝ → ℂ) (r : ℝ)
    (hz : spectralPhysicalLiouvillePair f g r = 0) : harmonicRadialState f g r = 0 := by
  have hp := congrArg (fun q : (ℂ × ℂ) × (ℂ × ℂ) => q.1.1) hz
  have hm := congrArg (fun q : (ℂ × ℂ) × (ℂ × ℂ) => q.2.1) hz
  have hdp := congrArg (fun q : (ℂ × ℂ) × (ℂ × ℂ) => q.1.2) hz
  have hdm := congrArg (fun q : (ℂ × ℂ) × (ℂ × ℂ) => q.2.2) hz
  change homogeneousSpectralLocalizationFactor 1 r*f r = 0 at hp
  change homogeneousSpectralLocalizationFactor (-1) r*g r = 0 at hm
  change homogeneousSpectralLocalizationFactor 1 r*
    (deriv f r+homogeneousSpectralLocalizationSlope 1 r*f r) = 0 at hdp
  change homogeneousSpectralLocalizationFactor (-1) r*
    (deriv g r+homogeneousSpectralLocalizationSlope (-1) r*g r) = 0 at hdm
  have hpf : f r = 0 := (mul_eq_zero.mp hp).resolve_left (Complex.exp_ne_zero _)
  have hmg : g r = 0 := (mul_eq_zero.mp hm).resolve_left (Complex.exp_ne_zero _)
  rw [hpf,mul_zero,add_zero] at hdp
  rw [hmg,mul_zero,add_zero] at hdm
  have hdf : deriv f r = 0 := (mul_eq_zero.mp hdp).resolve_left (Complex.exp_ne_zero _)
  have hdg : deriv g r = 0 := (mul_eq_zero.mp hdm).resolve_left (Complex.exp_ne_zero _)
  simp only [harmonicRadialState,hpf,hmg,hdf,hdg]
  rfl

theorem spectralPhysicalLiouvillePair_nonzero
    (a b : ℝ) (m : ℕ) (Q f g : ℝ → ℂ) (eta lam : ℂ)
    (hQ : ContinuousOn Q (Ioi 0)) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q eta lam f g)
    (hn : ∃ r : ℝ, 0 < r ∧ (f r ≠ 0 ∨ g r ≠ 0)) (R : ℝ) (hR : 0 < R) :
    spectralPhysicalLiouvillePair f g R ≠ 0 := by
  intro hz
  have hs := spectralPhysicalLiouvillePair_state_zero f g R hz
  obtain ⟨r,hr,hnr⟩ := hn
  have ht := harmonicRadialState_zero_of_zero a b m Q f g eta lam hQ hf hg he R hR hs r hr
  rcases hnr with hnr | hnr
  · exact hnr (congrArg (fun q : (ℂ × ℂ) × (ℂ × ℂ) => q.1.1) ht)
  · exact hnr (congrArg (fun q : (ℂ × ℂ) × (ℂ × ℂ) => q.2.1) ht)

end DefocusingNLS

end OAI
