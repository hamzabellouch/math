import OAI.NumberTheory.PrimePackets.ConditionalObservations

namespace OAI

/-! # Refining and recoding finite observations -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace PrimeDegreePackets

variable {Y α β γ δ : Type*} [MeasurableSpace Y]

lemma observationEntropy_injective [Fintype α] [Fintype β]
    (μ : Measure Y) (P : Y → α) (f : α → β) (hf : Function.Injective f) :
    observationEntropy μ (fun y => f (P y)) = observationEntropy μ P := by
  classical
  unfold observationEntropy finiteShannon
  symm
  apply Fintype.sum_of_injective f hf
  · intro b hb
    have hset : {y | f (P y) = b} = ∅ := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hb ⟨P y,h⟩
    simp [hset]
  · intro a
    simp only [hf.eq_iff]

lemma conditionalObservationEntropy_injective
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (μ : Measure Y) (P : Y → α) (Q : Y → β)
    (f : α → γ) (g : β → δ) (hf : Function.Injective f) (hg : Function.Injective g) :
    conditionalObservationEntropy μ (fun y => f (P y)) (fun y => g (Q y)) =
      conditionalObservationEntropy μ P Q := by
  unfold conditionalObservationEntropy
  rw [observationEntropy_injective μ Q g hg]
  have hi : Function.Injective (fun z : β × α => (g z.1,f z.2)) := by
    intro x y h
    exact Prod.ext (hg (congrArg Prod.fst h)) (hf (congrArg Prod.snd h))
  rw [observationEntropy_injective μ (fun y => (Q y,P y)) _ hi]

lemma conditionalObservationEntropy_comp_preserving [Fintype α] [Fintype β]
    (μ : Measure Y) (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b})
    {T : Y → Y} (hT : MeasurePreserving T μ μ) :
    conditionalObservationEntropy μ (fun y => P (T y)) (fun y => Q (T y)) =
      conditionalObservationEntropy μ P Q := by
  unfold conditionalObservationEntropy
  rw [observationEntropy_comp_preserving μ (fun y => (Q y,P y))
    (observationPair_measurable_fiber Q P hQ hP) hT,
    observationEntropy_comp_preserving μ Q hQ hT]

theorem conditionalObservationEntropy_coarsening_le
    [Fintype α] [Fintype β] [Fintype γ]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β) (f : β → γ)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    conditionalObservationEntropy μ P Q ≤
      conditionalObservationEntropy μ P (fun y => f (Q y)) := by
  have hfQ c : MeasurableSet {y | f (Q y) = c} := by
    have heq : {y | f (Q y) = c} = ⋃ b : {b // f b = c}, {y | Q y = b.val} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      exact ⟨fun h => ⟨⟨Q y,h⟩,rfl⟩, fun ⟨b,h⟩ => h ▸ b.property⟩
    rw [heq]
    exact MeasurableSet.iUnion (fun b => hQ b.val)
  have H := conditionalObservationEntropy_conditioning_le μ P (fun y => f (Q y)) Q
    hP hfQ hQ
  have hi : Function.Injective (fun b : β => (f b,b)) := by
    intro a b h
    exact congrArg Prod.snd h
  have heq := conditionalObservationEntropy_injective μ P Q id (fun b => (f b,b))
    Function.injective_id hi
  change conditionalObservationEntropy μ P (fun y => (f (Q y),Q y)) =
    conditionalObservationEntropy μ P Q at heq
  rw [heq] at H
  exact H

theorem conditionalObservationEntropy_pair_pair_le
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (P : Y → α) (R : Y → β) (Q : Y → γ) (S : Y → δ)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hR : ∀ b, MeasurableSet {y | R y = b})
    (hQ : ∀ c, MeasurableSet {y | Q y = c})
    (hS : ∀ d, MeasurableSet {y | S y = d}) :
    conditionalObservationEntropy μ (fun y => (P y,R y)) (fun y => (Q y,S y)) ≤
      conditionalObservationEntropy μ P Q + conditionalObservationEntropy μ R S := by
  have hQS := observationPair_measurable_fiber Q S hQ hS
  refine (conditionalObservationEntropy_pair_le μ P R (fun y => (Q y,S y))
    hP hR hQS).trans ?_
  exact add_le_add
    (conditionalObservationEntropy_coarsening_le μ P (fun y => (Q y,S y)) Prod.fst hP hQS)
    (conditionalObservationEntropy_coarsening_le μ R (fun y => (Q y,S y)) Prod.snd hR hQS)

lemma observationEntropy_le_add_conditional [Fintype α] [Fintype β]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    observationEntropy μ P ≤ observationEntropy μ Q + conditionalObservationEntropy μ P Q := by
  have H := conditionalObservationEntropy_nonneg μ Q P hQ hP
  unfold conditionalObservationEntropy at H ⊢
  rw [observationEntropy_swap μ P Q] at H
  linarith

end PrimeDegreePackets

end

end OAI
