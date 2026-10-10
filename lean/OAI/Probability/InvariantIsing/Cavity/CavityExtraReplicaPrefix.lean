import OAI.Probability.InvariantIsing.Cavity.CavityLabeledModelNumerator
import OAI.Probability.InvariantIsing.Cavity.CavityExtraReplicas

namespace OAI

/-! Extra replicas are tested by restriction to the original prefix.
This preserves the actual finite spectral observable when passing from
numerator moments to normalized cavity-spin expectations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityReplicaPrefixTest {m r d : ℕ} (k : ℕ)
    (F : SpectralBlock m r × (Fin r → Spin d) →ᵇ ℝ) :
    SpectralBlock m (r + k) × (Fin (r + k) → Spin d) →ᵇ ℝ :=
  F.compContinuous ⟨fun z =>
    ((fun i j => z.1 (Fin.castAdd k i) (Fin.castAdd k j)),
      fun i => z.2 (Fin.castAdd k i)), by fun_prop⟩

lemma cavity_extra_replica_identity_fin {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ)
    {r : ℕ} (F : (Fin r → X) → ℝ) (hw : Measurable w) (hF : Measurable F) (k : ℕ) :
    (∫ σ : Fin r → X, (∏ i, w (σ i)) * F σ ∂Measure.pi (fun _ => ν)) *
      (∫ x, w x ∂ν) ^ k =
    ∫ ξ : Fin (r + k) → X, (∏ i, w (ξ i)) * F (fun i => ξ (Fin.castAdd k i))
      ∂Measure.pi (fun _ => ν) := by
  rw [cavity_extra_replica_identity ν w F hw hF k]
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin r ⊕ Fin k => X) finSumFinEquiv.symm
  have hp : MeasurePreserving e (Measure.pi (fun _ : Fin (r + k) => ν))
      (Measure.pi (fun _ : Fin r ⊕ Fin k => ν)) :=
    measurePreserving_piCongrLeft (fun _ : Fin r ⊕ Fin k => ν) finSumFinEquiv.symm
  have hf : Measurable (fun ξ : (Fin r ⊕ Fin k) → X =>
      (∏ i, w (ξ i)) * F (fun i => ξ (.inl i))) :=
    (Finset.measurable_prod _ fun i _ => hw.comp (measurable_pi_apply i)).mul
      (hF.comp (Measurable.of_eval fun i : Fin r => measurable_pi_apply (Sum.inl i : Fin r ⊕ Fin k)))
  rw [← hp.hasLaw.integral_comp hf.aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    have heq (i : Fin r ⊕ Fin k) : e ξ i = ξ (finSumFinEquiv i) := by
      simpa only [Equiv.symm_apply_apply] using
        (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin r ⊕ Fin k => X) finSumFinEquiv.symm ξ (finSumFinEquiv i))
    dsimp only [Function.comp_apply]
    simp_rw [heq]
    rw [finSumFinEquiv.prod_comp (fun i => w (ξ i))]
    rfl

lemma cavityFiniteReplicaSpectralBlock_prefix {m n r k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (σ : Fin (r + k) → LabeledLeaf n) :
    (fun i j => cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ
      (Fin.castAdd k i) (Fin.castAdd k j)) =
      cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q (fun i => σ (Fin.castAdd k i)) := by
  funext i j a
  simp only [cavityFiniteReplicaSpectralBlock, cavitySynchronizedBlock, Fin.castAdd_inj]

lemma cavityLabeledReplicaTest_prefix {m n r k d qdim : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ)
    (F : SpectralBlock m r × (Fin r → Spin d) →ᵇ ℝ)
    (ω : CavityLabeledDisorder qdim n) (ξ : Fin (r + k) → CavityLabeledState qdim d n) :
    cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q)
      (cavityReplicaPrefixTest k F) (ω, ξ) =
      cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q)
        F (ω, fun i => ξ (Fin.castAdd k i)) := by
  simp only [cavityLabeledReplicaTest, cavityReplicaPrefixTest,
    BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
    cavityFiniteReplicaSpectralBlock_prefix]


lemma cavityLabeledCappedNumerator_mul_normalizer {m n r k d qdim : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ)
    (K R : Matrix (Fin qdim) (Fin qdim) ℝ)
    (L : Matrix (Fin qdim) (Fin d) ℝ) (C : Matrix (Fin d) (Fin d) ℝ)
    (π : Measure (Spin d)) [IsProbabilityMeasure π] (τ : ℝ)
    (F : SpectralBlock m r × (Fin r → Spin d) →ᵇ ℝ) (ω : CavityLabeledDisorder qdim n) :
    cavityLabeledCappedNumerator n K R L C π τ
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q) F ω *
        (cavityWeightNormalizer (cavityLabeledPriorKernel n R π ω)
          (fun x => Real.exp (min (cavityLabeledPotential n K L C (ω, x)) τ)))^k =
      cavityLabeledCappedNumerator n K R L C π τ
        (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q)
        (cavityReplicaPrefixTest k F) ω := by
  unfold cavityLabeledCappedNumerator cavityWeightNumerator cavityWeightNormalizer
  rw [cavity_extra_replica_identity_fin (cavityLabeledPriorKernel n R π ω)
    (fun x => Real.exp (min (cavityLabeledPotential n K L C (ω, x)) τ))
    (fun ξ => cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q) F (ω, ξ))
    ((((measurable_cavityLabeledPotential n K L C).comp
      measurable_prodMk_left).min measurable_const).exp)
    ((measurable_cavityLabeledReplicaTest _ F).comp measurable_prodMk_left) k]
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    dsimp only
    rw [cavityLabeledReplicaTest_prefix]

end InvariantIsing

end

end OAI
