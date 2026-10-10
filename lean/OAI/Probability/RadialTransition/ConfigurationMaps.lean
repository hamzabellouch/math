import OAI.Probability.RadialTransition.ProductConfigurations

namespace OAI

universe uX uY

noncomputable section


open Filter MeasureTheory Set

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition
section MapConfigurations
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y]

def mapParticle (f : X → Y) (x : ParticleState X) : ParticleState Y := ⟨x.1, f ∘ x.2⟩

lemma measurable_mapParticle {f : X → Y} (hf : Measurable f) : Measurable (mapParticle f) := by
  apply measurable_particle_iff.mpr
  intro n
  exact (measurable_particle_mk n).comp (measurable_pi_iff.mpr (fun i => hf.comp (measurable_pi_apply i)))

lemma particleBase_map (μ : Measure X) [IsFiniteMeasure μ] (z : ℝ)
    {f : X → Y} (hf : Measurable f) :
    Measure.map (mapParticle f) (particleBase μ z) = particleBase (Measure.map f μ) z := by
  unfold particleBase
  rw [Measure.map_sum (measurable_mapParticle hf).aemeasurable]
  congr 1
  funext n
  rw [Measure.map_smul _ (measurable_mapParticle hf).aemeasurable,
    Measure.map_map (measurable_mapParticle hf) (measurable_particle_mk n)]
  congr 1
  rw [← Measure.pi_map_pi (fun _ : Fin n => hf.aemeasurable)]
  exact (Measure.map_map (measurable_particle_mk n)
    (show Measurable (fun x : Fin n → X => fun i => f (x i)) from
      measurable_pi_iff.mpr (fun i => hf.comp (measurable_pi_apply i)))).symm

end MapConfigurations
section FiniteFock
variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
variable (F : Multiset X → ℝ≥0∞) (hF : ContinuousConfiguration F)
include hF

lemma particleBase_zero_observable (z : ℝ) (s : Multiset X) :
    (∫⁻ x, F (s+particleMultiset x) ∂particleBase (0 : Measure X) z) = F s := by
  rw [lintegral_particleBase _ _ (continuous_particleObservable F hF s).measurable]
  rw [tsum_eq_single 0]
  · simp [particleMultiset, configurationMultiset]
  · intro n hn
    have hμ : Measure.pi (fun _ : Fin n => (0 : Measure X)) = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [Measure.pi_univ]
      simp [hn]
    rw [hμ, lintegral_zero_measure, mul_zero]

lemma particleBase_fin_sum_observable (n : ℕ) (μ : Fin n → Measure X)
    [∀ i, IsFiniteMeasure (μ i)] (z : ℝ) (s : Multiset X) :
    (∫⁻ x, F (s+particleMultiset x) ∂particleBase (∑ i, μ i) z) =
      ∫⁻ x, F (s+multiParticleMultiset x) ∂Measure.pi (fun i => particleBase (μ i) z) := by
  induction n generalizing s with
  | zero =>
    simp only [Fin.sum_univ_zero]
    rw [particleBase_zero_observable F hF]
    simp [multiParticleMultiset]
  | succ n ih =>
    rw [Fin.sum_univ_succ, particleBase_add_observable F hF]
    simp_rw [ih]
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ParticleState X) 0
    have hp := MeasurePreserving.symm e
      (measurePreserving_piFinSuccAbove (fun i => particleBase (μ i) z) 0)
    have hc := (continuous_multiParticleObservable F hF s (I := Fin (n+1))).measurable
    rw [← hp.lintegral_comp hc]
    change _ = ∫⁻ p : ParticleState X × (Fin n → ParticleState X),
      F (s+multiParticleMultiset (e.symm p))
        ∂(particleBase (μ 0) z).prod (Measure.pi (fun i => particleBase (μ i.succ) z))
    have hpmeas : Measurable (fun p : ParticleState X × (Fin n → ParticleState X) =>
      F (s+multiParticleMultiset (e.symm p))) := hc.comp e.symm.measurable
    rw [lintegral_prod _ hpmeas.aemeasurable]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro y
    congr 1
    simp [multiParticleMultiset, Fin.sum_univ_succ, e,
      MeasurableEquiv.piFinSuccAbove_symm_apply, add_assoc]

end FiniteFock
end RadialTransition

end

end OAI
