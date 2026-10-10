import OAI.GroupTheory.PolycyclicRecognition.Algebra.BackwardRecurrenceSets
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BackwardSwitchProbability

namespace OAI

/-! # Positive probability of all prescribed returns -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal NNReal

/-- Backward recurrence and independent sampling together. The thresholds
are the actual normalized masses of the subsequent retained sets. -/
theorem exists_backward_recurrence_probability
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
      (∀ j, j < h → S j ⊆ S (j + 1) ∧
        (μ (S (j + 1))).toReal ^ 2 / (2 * D j * (μ Q).toReal) ≤ (μ (S j)).toReal) ∧
      let τ := fun j => Real.toNNReal ((μ (S (j + 1))).toReal / (2 * D j * (μ Q).toReal))
      0 < switchThresholdProduct τ 0 h ∧
        ∀ x ∈ S 0, switchThresholdProduct τ 0 h ≤ survivingSwitchProbability σ S 0 h x := by
  obtain ⟨S, hlast, hsets, hstep⟩ := exists_backward_recurrence_sets μ σ Q hQfin hQpos
    K R hK hRfin hRpos hQR D hD hvol h A hA hAQ hApos
  refine ⟨S, hlast, hsets, fun j hj => ⟨(hstep j hj).1, (hstep j hj).2.1⟩, ?_⟩
  let τ := fun j => Real.toNNReal ((μ (S (j + 1))).toReal / (2 * D j * (μ Q).toReal))
  have hpos (j : ℕ) (hj : j < h) :
      0 < (μ (S (j + 1))).toReal / (2 * D j * (μ Q).toReal) :=
    div_pos (hsets (j + 1) (by omega)).2.2
      (mul_pos (mul_pos (by norm_num) (hD j)) hQpos)
  have hτ (j : ℕ) (hj : j < h) : 0 < τ j := by
    exact Real.toNNReal_pos.mpr (hpos j hj)
  refine ⟨switchThresholdProduct_pos τ 0 h (fun j _ hj => hτ j (by omega)), ?_⟩
  intro x hx
  apply switchThresholdProduct_le_survival σ S τ 0 h _ hx
  intro j hj y hy
  have hjh : j < h := by omega
  have hr := (hstep j hjh).2.2 y hy
  have hfin : twoSampleReturn (σ j) (S (j + 1)) y ≠ ∞ :=
    (twoSampleReturn_le_one (σ j) (S (j + 1)) y).trans_lt (by simp) |>.ne
  have hr' := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_toReal hfin] at hr'
  exact hr'

end PolycyclicRecognition

end

end OAI
