import OAI.Probability.RadialTransition.FockIntegral

namespace OAI

universe uX

noncomputable section


open Filter MeasureTheory Set

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition
section ProductConfigurations
variable {I : Type} [Fintype I] (X : I → Type uX) [∀ i, TopologicalSpace (X i)]

def configurationsEquiv : (Σ n : I → ℕ, ∀ i, Fin (n i) → X i) ≃ (∀ i, ParticleState (X i)) where
  toFun s i := ⟨s.1 i, s.2 i⟩
  invFun x := ⟨fun i => (x i).1, fun i => (x i).2⟩
  left_inv s := by cases s; rfl
  right_inv x := rfl

def configurationsHomeomorph : (Σ n : I → ℕ, ∀ i, Fin (n i) → X i) ≃ₜ (∀ i, ParticleState (X i)) :=
  (configurationsEquiv X).toHomeomorphOfContinuousOpen
    (continuous_sigma (fun _n => continuous_pi (fun i => continuous_sigmaMk.comp (continuous_apply i))))
    (isOpenMap_sigma.mpr (fun n => (Topology.IsOpenEmbedding.piMap
      (fun i => (Topology.IsOpenEmbedding.sigmaMk (i := n i) :
        Topology.IsOpenEmbedding (@Sigma.mk ℕ (fun k => Fin k → X i) (n i))))).isOpenMap))

end ProductConfigurations
section MultiObservable
variable {I : Type} [Fintype I] {X : Type uX} [TopologicalSpace X]

def multiParticleMultiset (x : I → ParticleState X) : Multiset X := ∑ i, particleMultiset (x i)

lemma continuous_multiParticleObservable (F : Multiset X → ℝ≥0∞)
    (hF : ContinuousConfiguration F) (s : Multiset X) :
    Continuous (fun x : I → ParticleState X => F (s+multiParticleMultiset x)) := by
  have hc : Continuous (fun x : Σ n : I → ℕ, ∀ i, Fin (n i) → X =>
      F (s+∑ i, configurationMultiset (x.2 i))) := by
    apply continuous_sigma
    intro n
    have hh := (hF s (Σ i, Fin (n i))).comp
      (show Continuous (fun x : ∀ i, Fin (n i) → X => fun p : Σ i, Fin (n i) => x p.1 p.2) from by
        exact continuous_pi (fun p => (continuous_apply p.2).comp (continuous_apply p.1)))
    simpa only [Function.comp_def, configurationMultiset, Fintype.sum_sigma] using hh
  exact hc.comp (configurationsHomeomorph (fun _ : I => X)).symm.continuous

end MultiObservable
end RadialTransition

end

end OAI
