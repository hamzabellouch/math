import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableBoundaryEntropy

namespace OAI

/-! # Chain rules with one countable conditioning label

Finite clipping of the conditioning label and the martingale limit extend
the finite chain rule without requiring finite entropy of that label.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma observationSigma_pair_eq {Y α β : Type*} [Countable α] [Countable β]
    (P : Y → α) (Q : Y → β) :
    observationSigma (fun y => (P y,Q y))=observationSigma P ⊔ observationSigma Q := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have hprod : (inferInstance : MeasurableSpace (α × β))=⊤ := by
    apply top_unique
    intro s _
    exact (Set.to_countable s).measurableSet
  unfold observationSigma
  rw [←hprod]
  exact MeasurableSpace.comap_prodMk P Q

theorem conditionalSigmaEntropy_chain_nat {Y α β : Type*}
    [MeasurableSpace Y] [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (R : Y → β) (hR : ∀ b, MeasurableSet {y | R y=b})
    (F : Y → ℕ) (hF : Measurable F) :
    conditionalSigmaEntropy μ (fun y => (P y,R y))
        (MeasurableSpace.comap F inferInstance) =
      conditionalSigmaEntropy μ P (MeasurableSpace.comap F inferInstance) +
        conditionalSigmaEntropy μ R
          (MeasurableSpace.comap F inferInstance ⊔ observationSigma P) := by
  let C := fun L : ℕ => fun y : Y => (heightClip F L y,P y)
  have hC (L : ℕ) (b : Fin (L+1) × α) : MeasurableSet {y | C L y=b} :=
    observationPair_measurable_fiber _ _
      (fun a => heightClip_measurable hF L (measurableSet_singleton a)) hP b
  have hCm : Monotone (fun L => observationSigma (C L)) := by
    intro L J hLJ
    simp only [C,observationSigma_pair_eq]
    exact sup_le_sup_right (heightClip_sigma_monotone F hLJ) _
  have hCg : (⨆ L, observationSigma (C L))=
      MeasurableSpace.comap F inferInstance ⊔ observationSigma P := by
    simp only [C,observationSigma_pair_eq]
    rw [iSup_sup_eq,heightClip_sigma_generate,iSup_const]
  have h₁ := conditional_heightClip_tendsto μ (fun y => (P y,R y))
    (observationPair_measurable_fiber P R hP hR) F hF
  have h₂ := conditional_heightClip_tendsto μ P hP F hF
  have h₃ := conditionalObservationEntropy_tendsto_sigma μ R hR C hC hCm
  rw [hCg] at h₃
  apply tendsto_nhds_unique h₁
  apply (h₂.add h₃).congr
  intro L
  exact (conditionalObservationEntropy_chain μ P R (heightClip F L)).symm

theorem conditionalSigmaEntropy_comp_preserving_nat {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (F : Y → ℕ) (hF : Measurable F) :
    conditionalSigmaEntropy μ (P ∘ T) (MeasurableSpace.comap (F ∘ T) inferInstance) =
      conditionalSigmaEntropy μ P (MeasurableSpace.comap F inferInstance) := by
  have h₁ := conditional_heightClip_tendsto μ (P ∘ T)
    (fun a => (hP a).preimage hT.measurable) (F ∘ T) (hF.comp hT.measurable)
  have h₂ := conditional_heightClip_tendsto μ P hP F hF
  apply tendsto_nhds_unique h₁
  apply h₂.congr
  intro L
  symm
  exact conditionalObservationEntropy_comp_preserving μ P (heightClip F L) hP
    (fun a => heightClip_measurable hF L (measurableSet_singleton a)) hT

end DukePrimeDegree

end

end OAI
