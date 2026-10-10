import OAI.MeasureTheory.Falconer.Estimates.FilteredLimit
import OAI.MeasureTheory.Falconer.Shells.MonotoneShellCriterion

namespace OAI

/-!
# Final reconstruction for filtered original-distance measures

The two analytic hypotheses below are the restoration estimate and shell
summability. The conclusion uses the positive intersection
of the original pair filters, with no projection of distances.
-/

namespace Falconer
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- The endgame of `asm:completion`, in a form permitting the decreasing pair
filters of the all-dimensional manuscript. -/
theorem positive_volume_of_filtered_shells {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (hf : Measurable f) (ρ : Measure X) [IsFiniteMeasure ρ]
    (G : ℕ → Set X) (hG : ∀ n, MeasurableSet (G n)) (hmono : Antitone G)
    (D : Set ℝ) (hD : MeasurableSet D)
    (hcarry : ρ (f ⁻¹' Dᶜ) = 0) (hpositive : 0 < ρ (⋂ n, G n))
    (τ : ℕ → FiniteMeasure ℝ)
    (herror : Summable (fun n =>
      (PlanarFalconer.variationDistance
        ⟨filteredPushforward f ρ (G n), inferInstance⟩ (τ (n+1))).toReal))
    (hshell : Summable (fun n => ‖PlanarFalconer.shellL2Term τ n‖)) :
    0 < volume D := by
  let α : ℕ → FiniteMeasure ℝ := fun n =>
    ⟨filteredPushforward f ρ (G n), inferInstance⟩
  let μ : FiniteMeasure ℝ := ⟨filteredPushforward f ρ (⋂ n, G n), inferInstance⟩
  have hα : Antitone (fun n => (α n : Measure ℝ)) :=
    antitone_filteredPushforward f hf ρ hmono
  have hle : ∀ n, (μ : Measure ℝ) ≤ α n := fun n =>
    filteredPushforward_mono f hf ρ (iInter_subset G n)
  have hac : (μ : Measure ℝ) ≪ volume :=
    PlanarFalconer.monotone_shell_criterion α τ μ hα hle
      (filteredPushforward_tail_mass_tendsto f hf ρ G hG hmono) herror hshell
  exact positive_volume_of_carried_measure D μ
    (filteredPushforward_positive f hf ρ hpositive)
    (filteredPushforward_carried f hf ρ _ hD hcarry) hac

end Falconer

end OAI
