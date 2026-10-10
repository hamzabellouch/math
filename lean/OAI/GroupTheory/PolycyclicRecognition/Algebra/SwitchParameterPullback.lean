import OAI.GroupTheory.PolycyclicRecognition.Algebra.SuccessfulParameterMass

namespace OAI

/-! # Pulling the successful event back to the original independent samples -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set

/-- Apply the prescribed sampling map in each of the two independent slots. -/
def mapSwitchParameters {A B : Type*} (f : ℕ → A → B) :
    (n k : ℕ) → SwitchParameters A k → SwitchParameters B k
  | _, 0, _ => PUnit.unit
  | n, k + 1, p => (f n p.1, f n p.2.1, mapSwitchParameters f (n + 1) k p.2.2)

theorem measurePreserving_mapSwitchParameters {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (f : ℕ → A → B) (τ : ℕ → Measure A) (σ : ℕ → Measure B)
    [∀ j, IsProbabilityMeasure (τ j)] [∀ j, IsProbabilityMeasure (σ j)]
    (hf : ∀ j, MeasurePreserving (f j) (τ j) (σ j)) (n k : ℕ) :
    MeasurePreserving (mapSwitchParameters f n k)
      (switchParameterLaw τ n k) (switchParameterLaw σ n k) := by
  induction k generalizing n with
  | zero =>
    refine ⟨measurable_const, ?_⟩
    simp [mapSwitchParameters, switchParameterLaw]
  | succ k ih => exact (hf n).prod ((hf n).prod (ih (n + 1)))

/-- The successful probability is unchanged by returning to the independent
samples that defined the increment laws. -/
theorem pullback_switch_event {A G : Type*} [MeasurableSpace A]
    [Group G] [MeasurableSpace G]
    (f : ℕ → A → G) (τ : ℕ → Measure A) (σ : ℕ → Measure G)
    [∀ j, IsProbabilityMeasure (τ j)] [∀ j, IsProbabilityMeasure (σ j)]
    (hf : ∀ j, MeasurePreserving (f j) (τ j) (σ j))
    (n k : ℕ) (E : Set (SwitchParameters G k)) (hE : MeasurableSet E) :
    MeasurableSet (mapSwitchParameters f n k ⁻¹' E) ∧
      switchParameterLaw τ n k (mapSwitchParameters f n k ⁻¹' E) =
        switchParameterLaw σ n k E := by
  have h := measurePreserving_mapSwitchParameters f τ σ hf n k
  exact ⟨hE.preimage h.measurable, h.measure_preimage hE.nullMeasurableSet⟩

end PolycyclicRecognition

end

end OAI
