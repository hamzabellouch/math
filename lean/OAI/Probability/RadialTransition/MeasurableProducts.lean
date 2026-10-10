import OAI.Probability.RadialTransition.MeasurableFock

namespace OAI

universe uX uY

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition
section GeneralFock
variable {I : Type} [Fintype I] {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

lemma particleBase_sum_observable_meas (F : Multiset X → ℝ≥0∞) (hF : MeasurableConfiguration F)
    (μ : I → Measure X) [∀ i, IsFiniteMeasure (μ i)] (z : ℝ) (s : Multiset X) :
    (∫⁻ x, F (s+particleMultiset x) ∂particleBase (∑ i, μ i) z) =
      ∫⁻ x, F (s+multiParticleMultiset x) ∂Measure.pi (fun i => particleBase (μ i) z) := by
  let e := (Fintype.equivFin I).symm
  have hs : (∑ i, μ i) = ∑ j, μ (e j) := (e.sum_comp μ).symm
  rw [hs, particleBase_fin_sum_observable_meas F hF]
  have hp := measurePreserving_piCongrLeft (fun i => particleBase (μ i) z) e
  rw [← hp.lintegral_comp (measurable_multiParticleObservable F hF s)]
  apply lintegral_congr
  intro x
  congr 1
  dsimp [multiParticleMultiset, MeasurableEquiv.piCongrLeft]
  simpa [Equiv.piCongrLeft] using
    congrArg (fun q => s+q) (e.sum_comp (fun i => particleMultiset (x (e.symm i))))

variable (Y : I → Type uY) [∀ i, TopologicalSpace (Y i)] [∀ i, MeasurableSpace (Y i)]
  [∀ i, BorelSpace (Y i)] [∀ i, SecondCountableTopology (Y i)]

lemma particleBase_sum_map_observable_meas (F : Multiset X → ℝ≥0∞) (hF : MeasurableConfiguration F)
    (ν : ∀ i, Measure (Y i)) [∀ i, IsFiniteMeasure (ν i)]
    (pos : ∀ i, Y i → X) (hpos : ∀ i, Measurable (pos i)) (z : ℝ) (s : Multiset X) :
    (∫⁻ x, F (s+particleMultiset x) ∂particleBase (∑ i, Measure.map (pos i) (ν i)) z) =
      ∫⁻ x, F (s+mappedMultiParticleMultiset Y pos x) ∂Measure.pi (fun i => particleBase (ν i) z) := by
  rw [particleBase_sum_observable_meas F hF]
  simp_rw [← particleBase_map _ _ (hpos _)]
  rw [← Measure.pi_map_pi (fun i => (measurable_mapParticle (hpos i)).aemeasurable)]
  exact lintegral_map (measurable_multiParticleObservable F hF s)
    (measurable_pi_iff.mpr (fun i => (measurable_mapParticle (hpos i)).comp (measurable_pi_apply i)))

end GeneralFock
end RadialTransition

end

end OAI
