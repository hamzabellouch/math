import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableConditioningChain

namespace OAI

/-! # The finite chain rule after increasing countable conditioning

This form applies to the actual whole-future sigma algebra by using the
finite encoded future blocks. It never assumes that the countable labels
have finite Shannon entropy.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditionalSigmaEntropy_chain_iSup_nat
    {Y α β : Type*} [mY : MeasurableSpace Y] [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (R : Y → β) (hR : ∀ b, MeasurableSet {y | R y=b})
    (F : ℕ → Y → ℕ) (hF : ∀ N, Measurable (F N))
    (hmono : Monotone (fun N => observationSigma (F N))) :
    conditionalSigmaEntropy (mY := mY) μ (fun y => (P y,R y))
        (⨆ N, observationSigma (F N)) =
      conditionalSigmaEntropy (mY := mY) μ P (⨆ N, observationSigma (F N)) +
        conditionalSigmaEntropy (mY := mY) μ R
          ((⨆ N, observationSigma (F N)) ⊔ observationSigma P) := by
  have hle (N : ℕ) : observationSigma (F N) ≤ mY := (hF N).comap_le
  have hpairmono : Monotone (fun N => observationSigma (F N) ⊔ observationSigma P) :=
    fun _ _ h => sup_le_sup_right (hmono h) _
  have hpairle (N : ℕ) : observationSigma (F N) ⊔ observationSigma P ≤ mY :=
    sup_le (hle N) (observationSigma_le P hP)
  have h₁ := conditionalSigmaEntropy_tendsto_iSup μ (fun y => (P y,R y)) _ hmono hle
  have h₂ := conditionalSigmaEntropy_tendsto_iSup μ P _ hmono hle
  have h₃ := conditionalSigmaEntropy_tendsto_iSup μ R _ hpairmono hpairle
  rw [iSup_sup_eq,iSup_const] at h₃
  apply tendsto_nhds_unique h₁
  apply (h₂.add h₃).congr
  intro N
  exact (conditionalSigmaEntropy_chain_nat μ P hP R hR (F N) (hF N)).symm

theorem conditionalSigmaEntropy_comp_preserving_iSup_nat
    {Y α : Type*} [mY : MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (F : ℕ → Y → ℕ) (hF : ∀ N, Measurable (F N))
    (hmono : Monotone (fun N => observationSigma (F N)))
    (hmonoT : Monotone (fun N => observationSigma (F N ∘ T))) :
    conditionalSigmaEntropy (mY := mY) μ (P ∘ T)
        (⨆ N, observationSigma (F N ∘ T)) =
      conditionalSigmaEntropy (mY := mY) μ P (⨆ N, observationSigma (F N)) := by
  have h₁ := conditionalSigmaEntropy_tendsto_iSup μ (P ∘ T) _ hmonoT
    (fun N => ((hF N).comp hT.measurable).comap_le)
  have h₂ := conditionalSigmaEntropy_tendsto_iSup μ P _ hmono
    (fun N => (hF N).comap_le)
  apply tendsto_nhds_unique h₁
  apply h₂.congr
  intro N
  exact (conditionalSigmaEntropy_comp_preserving_nat μ hT P hP (F N) (hF N)).symm

end DukePrimeDegree

end

end OAI
