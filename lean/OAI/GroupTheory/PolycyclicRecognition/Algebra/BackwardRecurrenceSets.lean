import OAI.GroupTheory.PolycyclicRecognition.Algebra.BackwardRecurrenceStep

namespace OAI

/-! # Nested positive-measure sets for a fixed sequence of switches -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- Iterating the quantitative return estimate backwards produces the
nested sets used in the segment-volume argument. The number and order of
the increment laws are fixed before this construction. -/
theorem exists_backward_recurrence_sets
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (σ : ℕ → Measure G) [∀ j, IsProbabilityMeasure (σ j)]
    (Q : Set G) (hQfin : μ Q ≠ ∞) (hQpos : 0 < (μ Q).toReal)
    (K R : ℕ → Set G) (hK : ∀ j, ∀ᵐ s ∂σ j, s ∈ K j)
    (hRfin : ∀ j, μ (R j) ≠ ∞) (hRpos : ∀ j, 0 < (μ (R j)).toReal)
    (hQR : ∀ j, ∀ a ∈ Q, ∀ s ∈ K j, a * s ∈ R j)
    (D : ℕ → ℝ) (hD : ∀ j, 0 < D j)
    (hvol : ∀ j, (μ (R j)).toReal ≤ D j * (μ Q).toReal)
    (h : ℕ) (A : Set G) (hA : MeasurableSet A) (hAQ : A ⊆ Q)
    (hApos : 0 < (μ A).toReal) :
    ∃ S : ℕ → Set G, S h = A ∧
      (∀ j, j ≤ h → MeasurableSet (S j) ∧ S j ⊆ A ∧ 0 < (μ (S j)).toReal) ∧
      ∀ j, j < h → S j ⊆ S (j + 1) ∧
        (μ (S (j + 1))).toReal ^ 2 / (2 * D j * (μ Q).toReal) ≤ (μ (S j)).toReal ∧
        ∀ x ∈ S j, (μ (S (j + 1))).toReal / (2 * D j * (μ Q).toReal) ≤
          (twoSampleReturn (σ j) (S (j + 1)) x).toReal := by
  induction h generalizing A with
  | zero =>
    refine ⟨fun _ => A, rfl, ?_, ?_⟩
    · intro j hj
      exact ⟨hA, Subset.rfl, hApos⟩
    · intro j hj
      omega
  | succ h ih =>
    obtain ⟨B, hBm, hBA, hBpos, hmass, hreturn⟩ :=
      exists_backward_recurrence_step μ (σ h) A Q (K h) (R h) hA hQfin hAQ hApos hQpos
        (hK h) (hRfin h) (hRpos h) (fun a ha => hQR h a (hAQ ha)) (hD h) (hvol h)
    obtain ⟨S, hSh, hprop, hstep⟩ := ih B hBm (hBA.trans hAQ) hBpos
    let S' := fun j => if j ≤ h then S j else A
    have hlow (j : ℕ) (hj : j ≤ h) : S' j = S j := by simp only [S', hj, ite_true]
    have hlast : S' (h + 1) = A := by simp only [S', show ¬ h + 1 ≤ h by omega, ite_false]
    refine ⟨S', hlast, ?_, ?_⟩
    · intro j hj
      by_cases hjh : j ≤ h
      · rw [hlow j hjh]
        exact ⟨(hprop j hjh).1, (hprop j hjh).2.1.trans hBA, (hprop j hjh).2.2⟩
      · have heq : j = h + 1 := by omega
        rw [heq, hlast]
        exact ⟨hA, Subset.rfl, hApos⟩
    · intro j hj
      by_cases hjh : j < h
      · rw [hlow j (by omega), hlow (j + 1) (by omega)]
        exact hstep j hjh
      · have heq : j = h := by omega
        rw [heq, hlow h le_rfl, hlast, hSh]
        exact ⟨hBA, hmass, hreturn⟩

end PolycyclicRecognition

end

end OAI
