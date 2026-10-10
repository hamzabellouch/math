import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteSwitchEvents
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BackwardRecurrenceFamily

namespace OAI

/-! # Measurable successful parameter sets of subexponential probability

The starting point is chosen in the actual retained Haar-positive sheet.
Every intermediate state stays in the original good set. No independence
is claimed after restricting the independent product law to this event.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

theorem exists_subexponential_successful_parameters
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (σ : ℝ → ℕ → Measure G) [∀ r j, IsProbabilityMeasure (σ r j)]
    (Q A : ℝ → Set G) (K R : ℝ → ℕ → Set G) (D : ℝ → ℕ → ℝ)
    (hQfin : ∀ r, μ (Q r) ≠ ∞) (hQpos : ∀ r, 0 < (μ (Q r)).toReal)
    (hK : ∀ r j, ∀ᵐ s ∂σ r j, s ∈ K r j)
    (hRfin : ∀ r j, μ (R r j) ≠ ∞) (hRpos : ∀ r j, 0 < (μ (R r j)).toReal)
    (hQR : ∀ r j, ∀ a ∈ Q r, ∀ s ∈ K r j, a * s ∈ R r j)
    (hD : ∀ r j, 0 < D r j)
    (hvol : ∀ r j, (μ (R r j)).toReal ≤ D r j * (μ (Q r)).toReal)
    (h : ℕ) (hA : ∀ r, MeasurableSet (A r)) (hAQ : ∀ r, A r ⊆ Q r)
    (hApos : ∀ r, 0 < (μ (A r)).toReal)
    (hAlower : HasSubexponentialLowerBound (fun r => (μ (A r)).toReal / (μ (Q r)).toReal))
    (hDupper : ∀ j, j < h → HasSubexponentialUpperBound (fun r => D r j)) :
    ∃ (x : ℝ → G) (E : ℝ → Set (SwitchParameters G h)),
      (∀ r, x r ∈ A r) ∧ (∀ r, MeasurableSet (E r)) ∧
      HasSubexponentialLowerBound (fun r => (switchParameterLaw (σ r) 0 h (E r)).toReal) ∧
      ∀ r p, p ∈ E r → SwitchSuccessful (fun _ => A r) 0 h (x r) p := by
  obtain ⟨S, hlast, hS, _, hprob, hlower⟩ := exists_subexponential_backward_recurrence
    μ σ Q A K R D hQfin hQpos hK hRfin hRpos hQR hD hvol h hA hAQ hApos hAlower hDupper
  have hnonempty (r : ℝ) : (S r 0).Nonempty :=
    nonempty_of_measure_ne_zero (ne_of_gt (ENNReal.toReal_pos_iff.mp ((hS r 0 (Nat.zero_le h)).2.2)).1)
  choose x hx using hnonempty
  let E := fun r => {p : SwitchParameters G h | SwitchSuccessful (S r) 0 h (x r) p}
  have hevent (r : ℝ) := switchParameterLaw_success_finite (σ r) (S r) 0 h
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
