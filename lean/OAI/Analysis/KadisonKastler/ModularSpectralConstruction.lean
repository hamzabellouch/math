import OAI.Analysis.KadisonKastler.ModularNormalization
import OAI.Analysis.KadisonKastler.ConstructedModularData
import OAI.Analysis.KadisonKastler.HilbertConjugation

namespace OAI

/-! # The published modular spectral input, fully constructed

The bounded Tomita resolvent supplies the group, spectral cuts and Fourier
gauge identity. The bounded-equation averaging argument supplies normalization
and the polar commutant identity. No modular-theory premise remains.
-/

namespace KadisonKastler

noncomputable section

universe u

theorem publishedModularSpectralResolution : PublishedModularSpectralResolution.{u} := by
  intro H _ _ _ _ M Ω hcyc hsep
  obtain ⟨J, _⟩ := exists_hilbert_conjugation (H := H)
  exact ⟨constructedModularConjugationData J Ω hsep hcyc
      (tomitaPolarConjugation_commutant_eq J Ω hsep hcyc),
    constructedModularSpectralResolution J Ω hsep hcyc
      (modularStrongGroup_normalizes J Ω hsep hcyc)⟩

end

end KadisonKastler

end OAI
