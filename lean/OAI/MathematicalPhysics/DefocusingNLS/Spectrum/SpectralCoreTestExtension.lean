import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoreTestDensity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicCoreInverse

namespace OAI

/-! The weighted core inverse is determined by tests supported away from the core. -/

open MeasureTheory Filter Topology
namespace DefocusingNLS

theorem spectralHarmonicCore_equation_of_separated (ell : ℕ) (R l : ℝ)
    (hl : 0 < l) (hlR : l < R) (w : SpectralHarmonicWeight R)
    (u : SpectralHarmonicPair ell R) (F : StrongDual ℝ (SpectralHarmonicPair ell R))
    (he : ∀ (δ : ℝ), 0 < δ → ∀ v ∈ spectralHarmonicCoreSubspace ell R (l+δ),
      spectralHarmonicPairForm ell R w u v=F v) :
    ∀ v ∈ spectralHarmonicCoreSubspace ell R l, spectralHarmonicPairForm ell R w u v=F v := by
  intro v hv
  obtain ⟨vₙ,hlim,hvₙ⟩ := spectralHarmonicCore_test_dense ell R l hl hlR v hv
  have hn (n : ℕ) : spectralHarmonicPairForm ell R w u (vₙ n)=F (vₙ n) := by
    obtain ⟨δ,hδ,hmem⟩ := hvₙ n
    exact he δ hδ (vₙ n) hmem
  have hB := (spectralHarmonicPairForm ell R w u).continuous.continuousAt.tendsto.comp hlim
  have hF := F.continuous.continuousAt.tendsto.comp hlim
  exact tendsto_nhds_unique hB (hF.congr (fun n => (hn n).symm))

theorem spectralHarmonicCoreInverse_unique_separated (ell : ℕ) (R l : ℝ)
    (hl : 0 < l) (hlR : l < R) (w : SpectralHarmonicWeight R)
    (c : ℝ) (hc : 0 < c)
    (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r)
    (F : StrongDual ℝ (SpectralHarmonicPair ell R)) (u : SpectralHarmonicPair ell R)
    (hu : u ∈ spectralHarmonicCoreSubspace ell R l)
    (he : ∀ (δ : ℝ), 0 < δ → ∀ v ∈ spectralHarmonicCoreSubspace ell R (l+δ),
      spectralHarmonicPairForm ell R w u v=F v) :
    u=spectralHarmonicCoreInverse ell R l w c hc hcr hca F := by
  apply spectralHarmonicCoreInverse_unique ell R l w c hc hcr hca F u hu
  intro v
  exact spectralHarmonicCore_equation_of_separated ell R l hl hlR w u F he v v.property

end DefocusingNLS

end OAI
