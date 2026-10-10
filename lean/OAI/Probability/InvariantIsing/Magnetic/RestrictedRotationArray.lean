import OAI.Probability.InvariantIsing.Cavity.CavityRotationArray
import OAI.Probability.InvariantIsing.Magnetic.RestrictedRotationProbability

namespace OAI

/-! The spectral array sampled from the actual constrained base Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def restrictedRotationArrayLaw {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (ρ : Measure (LabeledTree depth)) [IsProbabilityMeasure ρ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    ProbabilityMeasure (SpectralArray (m+1)) :=
  ⟨(disorderReplicaLaw ((μ.prod ρ).prod gaussianCoordinates)
    (restrictedRotationProbability S hS eig I u) (measurable_restrictedRotationProbability S hS eig I u)).map
      (cavitySampledEntryArray (cavityRotationEntry I)),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_cavitySampledEntryArray (cavityRotationEntry I)
        (measurable_cavityRotationEntry I)).aemeasurable).mpr inferInstance⟩

lemma restrictedRotationArrayLaw_gram {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (ρ : Measure (LabeledTree depth)) [IsProbabilityMeasure ρ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    ∀ᵐ x ∂(restrictedRotationArrayLaw S hS μ ρ eig I u : Measure (SpectralArray (m+1))),
      SpectralGram x := by
  rw [restrictedRotationArrayLaw]
  apply (ae_map_iff (measurable_cavitySampledEntryArray (cavityRotationEntry I)
    (measurable_cavityRotationEntry I)).aemeasurable
    (isClosed_spectralGram (m+1)).measurableSet).mpr
  exact ae_of_all _ (cavityRotationEntry_gram I)

end InvariantIsing

end

end OAI
