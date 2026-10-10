import OAI.GroupTheory.PolycyclicRecognition.Algebra.BackwardRecurrenceStep

namespace OAI

/-! # Probability of retaining every intermediate sheet -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal NNReal

variable {G : Type*} [Group G] [MeasurableSpace G]

/-- Iterate the actual independent pairs of increment samples, killing a
path at its first exit from the prescribed next set. -/
def survivingSwitchProbability (σ : ℕ → Measure G) (S : ℕ → Set G) :
    ℕ → ℕ → G → ℝ≥0∞
  | _, 0, _ => 1
  | n, k + 1, x => ∫⁻ s₁, ∫⁻ s₂,
      (S (n + 1)).indicator (survivingSwitchProbability σ S (n + 1) k)
        (x * s₁ * s₂⁻¹) ∂σ n ∂σ n

/-- The product of the successive transition thresholds, in the same
recursive order as the independent sampling. -/
def switchThresholdProduct (τ : ℕ → ℝ≥0) : ℕ → ℕ → ℝ≥0∞
  | _, 0 => 1
  | n, k + 1 => τ n * switchThresholdProduct τ (n + 1) k

theorem switchThresholdProduct_ne_top (τ : ℕ → ℝ≥0) (n k : ℕ) :
    switchThresholdProduct τ n k ≠ ∞ := by
  induction k generalizing n with
  | zero => simp [switchThresholdProduct]
  | succ k ih => exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ih (n + 1))

theorem switchThresholdProduct_pos (τ : ℕ → ℝ≥0) (n k : ℕ)
    (hτ : ∀ j, n ≤ j → j < n + k → 0 < τ j) :
    0 < switchThresholdProduct τ n k := by
  induction k generalizing n with
  | zero => simp [switchThresholdProduct]
  | succ k ih =>
    apply ENNReal.mul_pos
    · exact_mod_cast (hτ n le_rfl (by omega)).ne'
    · exact (ih (n + 1) (fun j hj hj' => hτ j (by omega) (by omega))).ne'

theorem survivingSwitchProbability_le_one
    (σ : ℕ → Measure G) [∀ j, IsProbabilityMeasure (σ j)]
    (S : ℕ → Set G) (n k : ℕ) (x : G) :
    survivingSwitchProbability σ S n k x ≤ 1 := by
  induction k generalizing n x with
  | zero => rfl
  | succ k ih =>
    calc
      _ ≤ ∫⁻ _ : G, ∫⁻ _ : G, (1 : ℝ≥0∞) ∂σ n ∂σ n := by
        apply lintegral_mono
        intro s₁
        apply lintegral_mono
        intro s₂
        by_cases hy : x * s₁ * s₂⁻¹ ∈ S (n + 1)
        · simpa only [indicator_of_mem hy] using ih (n + 1) (x * s₁ * s₂⁻¹)
        · simp only [indicator_of_notMem hy, zero_le]
      _ = 1 := by simp

theorem measurable_survivingSwitchProbability
    [MeasurableMul₂ G] [MeasurableInv G]
    (σ : ℕ → Measure G) [∀ j, SFinite (σ j)]
    (S : ℕ → Set G) (hS : ∀ j, MeasurableSet (S j)) (n k : ℕ) :
    Measurable (survivingSwitchProbability σ S n k) := by
  induction k generalizing n with
  | zero => exact measurable_const
  | succ k ih =>
    have hchi := (ih (n + 1)).indicator (hS (n + 1))
    have hm := measurable_rightInverseAverage (σ n) hchi
    exact Measurable.lintegral_prod_right (f := fun x s : G =>
      rightInverseAverage (σ n)
        ((S (n + 1)).indicator (survivingSwitchProbability σ S (n + 1) k)) (x * s))
      (hm.comp (measurable_fst.mul measurable_snd))

/-- Independent sampling multiplies the conditional return bounds. The
sets may differ at each stage, which is essential for backward recurrence. -/
theorem switchThresholdProduct_le_survival
    (σ : ℕ → Measure G) (S : ℕ → Set G) (τ : ℕ → ℝ≥0)
    (n k : ℕ)
    (hreturn : ∀ j, j < n + k → ∀ x ∈ S j,
      (τ j : ℝ≥0∞) ≤ twoSampleReturn (σ j) (S (j + 1)) x)
    {x : G} (hx : x ∈ S n) :
    switchThresholdProduct τ n k ≤ survivingSwitchProbability σ S n k x := by
  induction k generalizing n x with
  | zero => rfl
  | succ k ih =>
    let P := switchThresholdProduct τ (n + 1) k
    have hP : P ≠ ∞ := switchThresholdProduct_ne_top τ (n + 1) k
    have hnext (y : G) (hy : y ∈ S (n + 1)) :
        P ≤ survivingSwitchProbability σ S (n + 1) k y := by
      apply ih (n + 1) (fun j hj => hreturn j (by omega)) hy
    have hbound : P * twoSampleReturn (σ n) (S (n + 1)) x ≤
        survivingSwitchProbability σ S n (k + 1) x := by
      calc
        _ = ∫⁻ s₁, ∫⁻ s₂,
            P * (S (n + 1)).indicator (fun _ => (1 : ℝ≥0∞)) (x * s₁ * s₂⁻¹)
              ∂σ n ∂σ n := by
          rw [twoSampleReturn, ← lintegral_const_mul' P _ hP]
          apply lintegral_congr
          intro s₁
          exact (lintegral_const_mul' P _ hP).symm
        _ ≤ _ := by
          apply lintegral_mono
          intro s₁
          apply lintegral_mono
          intro s₂
          by_cases hy : x * s₁ * s₂⁻¹ ∈ S (n + 1)
          · simpa only [indicator_of_mem hy, mul_one] using hnext _ hy
          · simp only [indicator_of_notMem hy, mul_zero, le_refl]
    change (τ n : ℝ≥0∞) * P ≤ _
    calc
      _ = P * (τ n : ℝ≥0∞) := mul_comm _ _
      _ ≤ P * twoSampleReturn (σ n) (S (n + 1)) x :=
        mul_le_mul' le_rfl (hreturn n (by omega) x hx)
      _ ≤ _ := hbound

end PolycyclicRecognition

end

end OAI
