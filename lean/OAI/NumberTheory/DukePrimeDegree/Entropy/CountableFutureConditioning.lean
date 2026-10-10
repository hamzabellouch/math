import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureSigmaAlgebra
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalSigmaLimit

namespace OAI

/-! # Finite approximation of a countable future observation

The countable geometric observations can be used for conditioning without
assuming finite Shannon entropy. Their conditioning sigma algebra is the
increasing limit of finite observations, and finite-label conditional
entropy converges along this limit.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

variable {Y : Type*} [mY : MeasurableSpace Y]

def finiteCountableObservation (Q : Y → ℕ) (m : ℕ) :
    Y → Fin (Fintype.card (Fin m → Bool)) :=
  finiteGeneratingObservation ℕ m ∘ Q

lemma finiteCountableObservation_measurable {Q : Y → ℕ} (hQ : Measurable Q) (m : ℕ) :
    Measurable (finiteCountableObservation Q m) :=
  (finiteGeneratingObservation_measurable ℕ m).comp hQ

omit mY in
lemma finiteCountableObservation_monotone (Q : Y → ℕ) :
    Monotone (fun m => observationSigma (finiteCountableObservation Q m)) := by
  intro m n hmn
  simp only [finiteCountableObservation,observationSigma_comp_eq_comap]
  exact MeasurableSpace.comap_mono (finiteGeneratingObservation_monotone ℕ hmn)

omit mY in
lemma finiteCountableObservation_generate (Q : Y → ℕ) :
    (⨆ m, observationSigma (finiteCountableObservation Q m)) = observationSigma Q := by
  simp only [finiteCountableObservation,observationSigma_comp_eq_comap]
  rw [←MeasurableSpace.comap_iSup,finiteGeneratingObservation_generate]
  rfl

omit mY in
lemma finiteCountableFuture_generate (T : Y → Y) (Q : Y → ℕ) :
    (⨆ m, ⨆ k : ℕ, observationSigma
      (fun x => finiteCountableObservation Q m (T^[k+1] x))) =
      ⨆ k : ℕ, observationSigma (fun x => Q (T^[k+1] x)) := by
  rw [iSup_comm]
  congr 1
  funext k
  have H := finiteCountableObservation_generate (fun x => Q (T^[k+1] x))
  exact H

/-- Only the observed finite label needs finite entropy. The extra future
observation may take countably many values. -/
theorem conditionalSigmaEntropy_countableFuture_limit {α : Type*} [Fintype α]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α)
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    (m₀ : MeasurableSpace Y) (hm₀ : m₀ ≤ mY) :
    Tendsto (fun m => conditionalSigmaEntropy (mY := mY) μ P
      (m₀ ⊔ ⨆ k : ℕ, observationSigma
        (fun x => finiteCountableObservation Q m (T^[k+1] x)))) atTop
      (𝓝 (conditionalSigmaEntropy (mY := mY) μ P
        (m₀ ⊔ ⨆ k : ℕ, observationSigma (fun x => Q (T^[k+1] x))))) := by
  have hmono : Monotone (fun m => m₀ ⊔ ⨆ k : ℕ, observationSigma
      (fun x => finiteCountableObservation Q m (T^[k+1] x))) := by
    intro m n hmn
    apply sup_le_sup le_rfl
    apply iSup_le
    intro k
    apply le_iSup_of_le k
    exact finiteCountableObservation_monotone (fun x => Q (T^[k+1] x)) hmn
  have hle (m : ℕ) : (m₀ ⊔ ⨆ k : ℕ, observationSigma
      (fun x => finiteCountableObservation Q m (T^[k+1] x))) ≤ mY := by
    apply sup_le hm₀
    apply iSup_le
    intro k
    exact observationSigma_le (mY := mY) _ (fun a =>
      ((finiteCountableObservation_measurable (mY := mY) hQ m).comp (hT.iterate (k+1)))
        (measurableSet_singleton a))
  have H := conditionalSigmaEntropy_tendsto_iSup (mY := mY) μ P _ hmono hle
  rw [iSup_sup_eq,iSup_const,finiteCountableFuture_generate] at H
  exact H

end DukePrimeDegree

end

end OAI
