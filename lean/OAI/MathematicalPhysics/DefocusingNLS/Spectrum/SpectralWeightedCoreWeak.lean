import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicCoreInverse
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeakSubsequence

namespace OAI

/-! Compact observations of the weighted constrained inverse converge for weak inputs. -/

open MeasureTheory Filter Topology
namespace DefocusingNLS

theorem spectralHarmonicObservation_weakSequence (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (u : ℕ → SpectralHarmonicPair ell R) (u₀ : SpectralHarmonicPair ell R)
    (M : ℝ) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ L : SpectralHarmonicPair ell R →L[ℝ] ℝ,
      Tendsto (fun n => L (u n)) atTop (𝓝 (L u₀))) :
    Tendsto (fun n => spectralHarmonicObservation ell R hR (u n)) atTop
      (𝓝 (spectralHarmonicObservation ell R hR u₀)) := by
  exact spectralCompact_weakSequence ((spectralHarmonicObservation ell R hR).restrictScalars ℝ)
    (spectralHarmonicObservation_compact ell R hR) u u₀ M hu hweak

theorem spectralHarmonicFirstValue_weakSequence (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (u : ℕ → SpectralHarmonicPair ell R) (u₀ : SpectralHarmonicPair ell R)
    (M : ℝ) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ L : SpectralHarmonicPair ell R →L[ℝ] ℝ,
      Tendsto (fun n => L (u n)) atTop (𝓝 (L u₀))) :
    Tendsto (fun n => spectralHarmonicFirstValue ell R (u n)) atTop
      (𝓝 (spectralHarmonicFirstValue ell R u₀)) := by
  have hp : Continuous (fun z : SpectralRadialObservationSpace R => z.1.1) :=
    continuous_fst.fst
  exact hp.continuousAt.tendsto.comp
    (spectralHarmonicObservation_weakSequence ell R hR u u₀ M hu hweak)

theorem spectralHarmonicCoreInverse_weak_input (ell : ℕ) (R l : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (c : ℝ) (hc : 0 < c)
    (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r)
    (F : ℕ → StrongDual ℝ (SpectralHarmonicPair ell R))
    (F₀ : StrongDual ℝ (SpectralHarmonicPair ell R)) (M : ℝ) (hF : ∀ n, ‖F n‖ ≤ M)
    (hweak : ∀ L : StrongDual ℝ (SpectralHarmonicPair ell R) →L[ℝ] ℝ,
      Tendsto (fun n => L (F n)) atTop (𝓝 (L F₀))) :
    Tendsto (fun n => spectralHarmonicObservation ell R hR
      (spectralHarmonicCoreInverse ell R l w c hc hcr hca (F n))) atTop
      (𝓝 (spectralHarmonicObservation ell R hR
        (spectralHarmonicCoreInverse ell R l w c hc hcr hca F₀))) := by
  let T := spectralHarmonicCoreInverse ell R l w c hc hcr hca
  apply spectralHarmonicObservation_weakSequence ell R hR (fun n => T (F n)) (T F₀) (M/c)
  · intro n
    exact (spectralHarmonicCoreInverse_norm ell R l w c hc hcr hca (F n)).trans
      (div_le_div_of_nonneg_right (hF n) hc.le)
  · intro L
    exact hweak (L.comp T)

end DefocusingNLS

end OAI
