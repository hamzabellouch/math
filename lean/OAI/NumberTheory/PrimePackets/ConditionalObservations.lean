import OAI.NumberTheory.PrimePackets.ConditionalShannon

namespace OAI

/-!
# Conditional entropy of finite observations

The conditioning variable is the last argument. All identities below use
the actual distribution under `μ`, including its zero-mass cells.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace PrimeDegreePackets

variable {Y α β γ : Type*} [MeasurableSpace Y]

lemma observationPair_measurable_fiber (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    ∀ z, MeasurableSet {y | (P y,Q y) = z} := by
  rintro ⟨a,b⟩
  simpa only [Prod.mk.injEq, Set.ofPred_and] using (hP a).inter (hQ b)

def conditionalObservationEntropy [Fintype α] [Fintype β]
    (μ : Measure Y) (P : Y → α) (Q : Y → β) : ℝ :=
  observationEntropy μ (fun y => (Q y,P y)) - observationEntropy μ Q

lemma observationEntropy_swap [Fintype α] [Fintype β]
    (μ : Measure Y) (P : Y → α) (Q : Y → β) :
    observationEntropy μ (fun y => (P y,Q y)) =
      observationEntropy μ (fun y => (Q y,P y)) := by
  exact (observationEntropy_equiv μ (fun y => (P y,Q y)) (Equiv.prodComm α β)).symm

lemma observationEntropy_assoc [Fintype α] [Fintype β] [Fintype γ]
    (μ : Measure Y) (P : Y → α) (Q : Y → β) (R : Y → γ) :
    observationEntropy μ (fun y => ((P y,Q y),R y)) =
      observationEntropy μ (fun y => (P y,(Q y,R y))) := by
  exact (observationEntropy_equiv μ (fun y => ((P y,Q y),R y))
    (Equiv.prodAssoc α β γ)).symm

lemma conditionalObservationEntropy_nonneg [Fintype α] [Fintype β]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    0 ≤ conditionalObservationEntropy μ P Q := by
  have H := finiteShannon_fst_le
    (fun z : β × α => μ.real {y | (Q y,P y) = z}) (fun _ => measureReal_nonneg)
  simp only [observation_joint_row μ Q P hQ hP] at H
  exact sub_nonneg.mpr H

lemma conditionalObservationEntropy_le [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    conditionalObservationEntropy μ P Q ≤ observationEntropy μ P := by
  have H := observationEntropy_joint_le μ Q P hQ hP
  unfold conditionalObservationEntropy
  linarith

lemma conditionalObservationEntropy_chain [Fintype α] [Fintype β] [Fintype γ]
    (μ : Measure Y) (P : Y → α) (R : Y → β) (Q : Y → γ) :
    conditionalObservationEntropy μ (fun y => (P y,R y)) Q =
      conditionalObservationEntropy μ P Q +
      conditionalObservationEntropy μ R (fun y => (Q y,P y)) := by
  unfold conditionalObservationEntropy
  rw [observationEntropy_assoc]
  ring

theorem observationEntropy_submodular [Fintype α] [Fintype β] [Fintype γ]
    (μ : Measure Y) [IsFiniteMeasure μ] (Q : Y → α) (P : Y → β) (R : Y → γ)
    (hQ : ∀ a, MeasurableSet {y | Q y = a})
    (hP : ∀ b, MeasurableSet {y | P y = b})
    (hR : ∀ c, MeasurableSet {y | R y = c}) :
    observationEntropy μ (fun y => (Q y,(P y,R y))) + observationEntropy μ Q ≤
      observationEntropy μ (fun y => (Q y,P y)) +
      observationEntropy μ (fun y => (Q y,R y)) := by
  let p : α × (β × γ) → ℝ := fun z => μ.real {y | (Q y,(P y,R y)) = z}
  have hrow a : ∑ z : β × γ, p (a,z) = μ.real {y | Q y = a} :=
    observation_joint_row μ Q (fun y => (P y,R y)) hQ
      (observationPair_measurable_fiber P R hP hR) a
  have hleft (z : α × β) : ∑ c, p (z.1,(z.2,c)) = μ.real {y | (Q y,P y) = z} := by
    rcases z with ⟨a,b⟩
    convert observation_joint_row μ (fun y => (Q y,P y)) R
      (observationPair_measurable_fiber Q P hQ hP) hR (a,b) using 1
    apply Finset.sum_congr rfl
    intro c _
    apply congrArg μ.real
    ext y
    simp only [Prod.mk.injEq, Set.mem_ofPred_eq]
    tauto
  have hright (z : α × γ) : ∑ b, p (z.1,(b,z.2)) = μ.real {y | (Q y,R y) = z} := by
    rcases z with ⟨a,c⟩
    convert observation_joint_row μ (fun y => (Q y,R y)) P
      (observationPair_measurable_fiber Q R hQ hR) hP (a,c) using 1
    apply Finset.sum_congr rfl
    intro b _
    apply congrArg μ.real
    ext y
    simp only [Prod.mk.injEq, Set.mem_ofPred_eq]
    tauto
  have H := finiteShannon_submodular p (fun _ => measureReal_nonneg)
  simpa only [hrow, hleft, hright, observationEntropy] using H

theorem conditionalObservationEntropy_conditioning_le
    [Fintype α] [Fintype β] [Fintype γ]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β) (R : Y → γ)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b})
    (hR : ∀ c, MeasurableSet {y | R y = c}) :
    conditionalObservationEntropy μ P (fun y => (Q y,R y)) ≤
      conditionalObservationEntropy μ P Q := by
  have H := observationEntropy_submodular μ Q R P hQ hR hP
  unfold conditionalObservationEntropy
  rw [observationEntropy_assoc]
  linarith

theorem conditionalObservationEntropy_pair_le
    [Fintype α] [Fintype β] [Fintype γ]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (R : Y → β) (Q : Y → γ)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hR : ∀ b, MeasurableSet {y | R y = b})
    (hQ : ∀ c, MeasurableSet {y | Q y = c}) :
    conditionalObservationEntropy μ (fun y => (P y,R y)) Q ≤
      conditionalObservationEntropy μ P Q + conditionalObservationEntropy μ R Q := by
  rw [conditionalObservationEntropy_chain]
  exact add_le_add le_rfl (conditionalObservationEntropy_conditioning_le μ R Q P hR hQ hP)

end PrimeDegreePackets

end

end OAI
