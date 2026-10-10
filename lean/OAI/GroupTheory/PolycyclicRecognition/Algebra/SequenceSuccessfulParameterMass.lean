import OAI.GroupTheory.PolycyclicRecognition.Algebra.SuccessfulParameterMass
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceBackwardRecurrence

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem exists_subexponential_successful_parameters_sequence
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (σ : ℕ → ℕ → Measure G) [∀ r j, IsProbabilityMeasure (σ r j)]
    (Q A : ℕ → Set G) (K R : ℕ → ℕ → Set G) (D : ℕ → ℕ → ℝ)
    (hQfin : ∀ r, μ (Q r) ≠ ∞) (hQpos : ∀ r, 0 < (μ (Q r)).toReal)
    (hK : ∀ r j, ∀ᵐ s ∂σ r j, s ∈ K r j)
    (hRfin : ∀ r j, μ (R r j) ≠ ∞) (hRpos : ∀ r j, 0 < (μ (R r j)).toReal)
    (hQR : ∀ r j, ∀ a ∈ Q r, ∀ s ∈ K r j, a * s ∈ R r j)
    (hD : ∀ r j, 0 < D r j)
    (hvol : ∀ r j, (μ (R r j)).toReal ≤ D r j * (μ (Q r)).toReal)
    (h : ℕ) (hA : ∀ r, MeasurableSet (A r)) (hAQ : ∀ r, A r ⊆ Q r)
    (hApos : ∀ r, 0 < (μ (A r)).toReal)
    (hAlower : HasSubexponentialLowerBoundSeq scale (fun r => (μ (A r)).toReal / (μ (Q r)).toReal))
    (hDupper : ∀ j, j < h → HasSubexponentialUpperBoundSeq scale (fun r => D r j)) :
    ∃ (x : ℕ → G) (E : ℕ → Set (SwitchParameters G h)),
      (∀ r, x r ∈ A r) ∧ (∀ r, MeasurableSet (E r)) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (switchParameterLaw (σ r) 0 h (E r)).toReal) ∧
      ∀ r p, p ∈ E r → SwitchSuccessful (fun _ => A r) 0 h (x r) p := by
  obtain ⟨S, hlast, hS, _, hprob, hlower⟩ := exists_subexponential_backward_recurrence_sequence
    scale hscale μ σ Q A K R D hQfin hQpos hK hRfin hRpos hQR hD hvol h hA hAQ hApos hAlower hDupper
  have hnonempty (r : ℕ) : (S r 0).Nonempty :=
    nonempty_of_measure_ne_zero (ne_of_gt (ENNReal.toReal_pos_iff.mp ((hS r 0 (Nat.zero_le h)).2.2)).1)
  choose x hx using hnonempty
  let E := fun r => {p : SwitchParameters G h | SwitchSuccessful (S r) 0 h (x r) p}
  have hevent (r : ℕ) := switchParameterLaw_success_finite (σ r) (S r) 0 h
    (fun j _ hj => (hS r j (by simpa using hj)).1) (x r)
  refine ⟨x, E, fun r => (hS r 0 (Nat.zero_le h)).2.1 (hx r), fun r => (hevent r).1, ?_, ?_⟩
  · apply hprob.mono
    apply Eventually.of_forall
    intro r
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    rw [(hevent r).2]
    exact hlower r (x r) (hx r)
  · intro r p hp
    exact switchSuccessful_mono (S r) (fun _ => A r) 0 h
      (fun j _ hj => (hS r j (by simpa using hj)).2.1) (x r) p hp

end PolycyclicRecognition

end

end OAI
