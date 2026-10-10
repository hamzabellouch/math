import OAI.GroupTheory.PolycyclicRecognition.Analysis.BackwardRecurrenceProbability
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BackwardRecurrenceAsymptotics

namespace OAI

/-! # Backward recurrence for a varying family of Haar boxes -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

/-- The elementary change from Haar mass to relative Haar mass in the
quadratic recurrence. -/
theorem normalized_backward_mass_bound {a b q D : ℝ} (hq : 0 < q) (hD : 0 < D)
    (h : b ^ 2 / (2 * D * q) ≤ a) :
    (b / q) ^ 2 / (2 * D) ≤ a / q := by
  have heq : (b / q) ^ 2 / (2 * D) = (b ^ 2 / (2 * D * q)) / q := by
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right h hq.le

/-- The retained initial sheets and the probability of every successful
switch both have subexponential lower bounds. The groups and sampling laws
are actual measure spaces, and the good set may vary with scale. -/
theorem exists_subexponential_backward_recurrence
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
    ∃ S : ℝ → ℕ → Set G,
      (∀ r, S r h = A r) ∧
      (∀ r j, j ≤ h → MeasurableSet (S r j) ∧ S r j ⊆ A r ∧ 0 < (μ (S r j)).toReal) ∧
      HasSubexponentialLowerBound (fun r => (μ (S r 0)).toReal / (μ (Q r)).toReal) ∧
      let τ := fun r j => Real.toNNReal ((μ (S r (j + 1))).toReal /
        (2 * D r j * (μ (Q r)).toReal))
      HasSubexponentialLowerBound (fun r => (switchThresholdProduct (τ r) 0 h).toReal) ∧
        ∀ r x, x ∈ S r 0 →
          switchThresholdProduct (τ r) 0 h ≤ survivingSwitchProbability (σ r) (S r) 0 h x := by
  choose S hS using fun r => exists_backward_recurrence_probability μ (σ r) (Q r)
    (hQfin r) (hQpos r) (K r) (R r) (hK r) (hRfin r) (hRpos r) (hQR r)
    (D r) (hD r) (hvol r) h (A r) (hA r) (hAQ r) (hApos r)
  let a := fun j r => (μ (S r j)).toReal / (μ (Q r)).toReal
  have hlast : HasSubexponentialLowerBound (a h) := by
    simpa only [a, (hS _).1] using hAlower
  have hsteps (j : ℕ) (hj : j < h) : ∀ᶠ r in atTop,
      a (j + 1) r ^ 2 / (2 * D r j) ≤ a j r := by
    exact Eventually.of_forall (fun r => normalized_backward_mass_bound (hQpos r) (hD r j)
      ((hS r).2.2.1 j hj).2)
  have hpos (j : ℕ) (_ : j < h) : ∀ᶠ r in atTop, 0 < D r j :=
    Eventually.of_forall (fun r => hD r j)
  have hmasses := subexponential_backward_masses h a (fun j r => D r j)
    hlast hDupper hpos hsteps
  have hthresholds := subexponential_backward_thresholds h a (fun j r => D r j)
    hlast hDupper hpos hsteps
  let τ := fun r j => Real.toNNReal ((μ (S r (j + 1))).toReal /
    (2 * D r j * (μ (Q r)).toReal))
  have hτ (j : ℕ) (hj : j < h) :
      HasSubexponentialLowerBound (fun r => (τ r j : ℝ)) := by
    apply (hthresholds j hj).mono
    apply Eventually.of_forall
    intro r
    have heq : (τ r j : ℝ) = a (j + 1) r / (2 * D r j) := by
      have hp : 0 ≤ (μ (S r (j + 1))).toReal / (2 * D r j * (μ (Q r)).toReal) :=
        div_nonneg ENNReal.toReal_nonneg
          (mul_pos (mul_pos (by norm_num) (hD r j)) (hQpos r)).le
      change (Real.toNNReal ((μ (S r (j + 1))).toReal /
        (2 * D r j * (μ (Q r)).toReal)) : ℝ) =
        ((μ (S r (j + 1))).toReal / (μ (Q r)).toReal) / (2 * D r j)
      rw [Real.coe_toNNReal _ hp]
      ring
    exact heq.ge
  refine ⟨S, fun r => (hS r).1, fun r => (hS r).2.1, hmasses 0 (Nat.zero_le _), ?_⟩
  refine ⟨subexponential_switch_product (fun j r => τ r j) 0 h (fun j _ hj => hτ j (by omega)), ?_⟩
  exact fun r x hx => (hS r).2.2.2.2 x hx

end PolycyclicRecognition

end

end OAI
