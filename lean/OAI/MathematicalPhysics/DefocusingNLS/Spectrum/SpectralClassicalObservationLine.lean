import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClassicalPairing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeObservationLine

namespace OAI

/-! # Recovering proportional classical functions from compact observations -/

open Set

namespace DefocusingNLS

theorem spectralClassical_pair_eq_of_observation (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (u v : SpectralHarmonicPair ell R) (f g F G : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 R)) (hg : ContinuousOn g (Icc 0 R))
    (hF : ContinuousOn F (Icc 0 R)) (hG : ContinuousOn G (Icc 0 R))
    (huf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.fst r = f r)
    (hug : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.snd r = g r)
    (hvF : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR v.fst r = F r)
    (hvG : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR v.snd r = G r)
    (c : ℂ) (he : spectralHarmonicObservation ell R hR u =
      c • spectralHarmonicObservation ell R hR v) :
    ∀ r ∈ Icc 0 R, f r = c * F r ∧ g r = c * G r := by
  have hz : spectralHarmonicObservation ell R hR (u - c • v) = 0 := by
    rw [map_sub, map_smul, he, sub_self]
  have hzf : spectralHarmonicValue ell R (u.fst - c • v.fst) = 0 := by
    rw [spectralHarmonicObservation_coordinates] at hz
    exact congrArg (fun w => w.1.1) hz
  have hzg : spectralHarmonicValue ell R (u.snd - c • v.snd) = 0 := by
    rw [spectralHarmonicObservation_coordinates] at hz
    exact congrArg (fun w => w.1.2) hz
  have h1 := spectralHarmonicClassical_zero_of_value ell R hR (u.fst - c • v.fst)
    (fun r => f r - c * F r) (hf.sub (continuousOn_const.mul hF))
    (fun r hr => by rw [spectralHarmonicRepresentative_sub_smul, huf r hr, hvF r hr]) hzf
  have h2 := spectralHarmonicClassical_zero_of_value ell R hR (u.snd - c • v.snd)
    (fun r => g r - c * G r) (hg.sub (continuousOn_const.mul hG))
    (fun r hr => by rw [spectralHarmonicRepresentative_sub_smul, hug r hr, hvG r hr]) hzg
  intro r hr
  exact ⟨sub_eq_zero.mp (h1 r hr), sub_eq_zero.mp (h2 r hr)⟩

end DefocusingNLS

end OAI
