import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRepresentativeTrace

namespace OAI

/-! Vanishing positive-radius representatives annihilate the compact observation. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralHarmonicValue_zero_of_representative (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (u : SpectralHarmonicEnergy ell R)
    (hu : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u r=0) :
    spectralHarmonicValue ell R u=0 := by
  apply Lp.ext
  filter_upwards [spectralRadialRepresentative_ae R hR (spectralHarmonicRadialForget ell R u),
    radialPressureMeasure_ae_positive R, Lp.coeFn_zero ℂ 2 (radialPressureMeasure R)] with r hr hp hz
  change spectralRadialValue R (spectralHarmonicRadialForget ell R u) r=_
  rw [← hr]
  exact (hu r hp).trans hz.symm

theorem spectralHarmonicObservation_coordinates (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (u : SpectralHarmonicPair ell R) :
    spectralHarmonicObservation ell R hR u=
      ((spectralHarmonicValue ell R u.fst,spectralHarmonicValue ell R u.snd),
        (spectralHarmonicRepresentative ell R hR u.fst R,
          spectralHarmonicRepresentative ell R hR u.snd R)) := by
  rw [spectralHarmonicRepresentative_trace]
  rfl

theorem spectralHarmonicObservation_zero_of_representatives (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (u : SpectralHarmonicPair ell R)
    (hf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.fst r=0)
    (hg : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.snd r=0) :
    spectralHarmonicObservation ell R hR u=0 := by
  rw [spectralHarmonicObservation_coordinates,
    spectralHarmonicValue_zero_of_representative ell R hR u.fst hf,
    spectralHarmonicValue_zero_of_representative ell R hR u.snd hg,
    hf R ⟨hR,le_rfl⟩,hg R ⟨hR,le_rfl⟩]
  rfl

end DefocusingNLS

end OAI
