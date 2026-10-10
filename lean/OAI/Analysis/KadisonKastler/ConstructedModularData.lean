import OAI.Analysis.KadisonKastler.PublishedModularSpectral
import OAI.Analysis.KadisonKastler.ModularGaugeIdentity
import OAI.Analysis.KadisonKastler.ModularKMS
import OAI.Analysis.KadisonKastler.ModularCentralizerFixed
import OAI.Analysis.KadisonKastler.ModularCutBounds
import OAI.Analysis.KadisonKastler.TomitaCentralizerConjugation

namespace OAI

/-! # Assembling the constructed bounded modular data

The modular group and spectral cuts yield bounded modular data
when the group normalizes the algebra. Tomita conjugation gives the
conjugation data when it identifies the algebra with its commutant.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

/-- Spectral modular data for a modular group normalizing the algebra. -/
def constructedModularSpectralResolution
    (hnormal : ∀ t, Conjugates (modularStrongGroup J Ω hsep hcyc t) M M) :
    ModularSpectralResolution M Ω where
  group := modularStrongGroup J Ω hsep hcyc
  continuous := modularStrongGroup_continuous J Ω hsep hcyc
  normalizes := hnormal
  isModular := modularStrongGroup_isModular J Ω hsep hcyc
  centralizer_fixed := modularStrongGroup_centralizer_fixed J Ω hsep hcyc hnormal
  upperCut := modularUpperCut M J Ω
  projection := modularUpperCut_projection J Ω
  upper_contracts := modularUpperCut_contracts J Ω
  lower_contracts := modularUpperCut_complement_contracts J Ω
  measurable := modularUpperCut_measurable J Ω
  gauge_identity := modularGauge_identity J Ω hsep hcyc
  high_inverse K := modularUpperCut_high_inverse J K Ω
  low_bound K := modularUpperCut_low_bound J K Ω
  low_support K := modularUpperCut_low_support J K Ω

omit [TopologicalSpace.SeparableSpace H] in
/-- Modular conjugation data from the Tomita commutant identity. -/
def constructedModularConjugationData
    (hcomm : conjugateRightAlgebra (tomitaPolarConjugation J Ω hsep hcyc)
      (tomitaPolarConjugation_involutive J Ω hsep hcyc) M = M.commutant) :
    ModularConjugationData M Ω where
  conjugation := tomitaPolarConjugation J Ω hsep hcyc
  involutive := tomitaPolarConjugation_involutive J Ω hsep hcyc
  fixes_vector := tomitaPolarConjugation_fixes_vector J Ω hsep hcyc
  commutant := hcomm
  centralizer_vector r hr := by
    change tomitaPolarConjugation J Ω hsep hcyc
      (star r.val (tomitaPolarConjugation J Ω hsep hcyc Ω)) = r.val Ω
    rw [tomitaPolarConjugation_fixes_vector J Ω hsep hcyc]
    exact tomitaPolarConjugation_star_centralizer J Ω hsep hcyc r hr

end

end KadisonKastler

end OAI
