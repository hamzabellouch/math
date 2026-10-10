import Mathlib
import OAI.Probability.SphericalField.Perceptron.TimeLaw

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma log_integral_exp_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F G : Ω → ℝ} {c : ℝ}
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (pF : 0 < ∫ x, Real.exp (F x) ∂μ) (pG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (h : ∀ x, F x ≤ G x + c) :
    Real.log (∫ x, Real.exp (F x) ∂μ) - Real.log (∫ x, Real.exp (G x) ∂μ) ≤ c := by
  have hi : (∫ x, Real.exp (F x) ∂μ) ≤
      Real.exp c * ∫ x, Real.exp (G x) ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hF (hG.const_mul _)
    intro x
    calc
      Real.exp (F x) ≤ Real.exp (G x + c) := Real.exp_le_exp.mpr (h x)
      _ = Real.exp c * Real.exp (G x) := by rw [Real.exp_add, mul_comm]
  have hl := Real.log_le_log pF hi
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt pG), Real.log_exp] at hl
  linarith

lemma abs_log_integral_exp_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F G : Ω → ℝ} {c : ℝ}
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (pF : 0 < ∫ x, Real.exp (F x) ∂μ) (pG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (h : ∀ x, |F x - G x| ≤ c) :
    |Real.log (∫ x, Real.exp (F x) ∂μ) - Real.log (∫ x, Real.exp (G x) ∂μ)| ≤ c := by
  apply abs_le.mpr
  constructor
  · have hh := log_integral_exp_sub_le μ hG hF pG pF (fun x => by
      have := (abs_le.mp (h x)).1
      linarith)
    linarith
  · exact log_integral_exp_sub_le μ hF hG pF pG (fun x => by
      have := (abs_le.mp (h x)).2
      linarith)

lemma abs_energy_le (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α N) (x : Spin N) :
    |β * hamiltonian α φ N g x| ≤ |β| * (patternCount α N : ℝ) * ‖φ‖ := by
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_hamiltonian_le α φ N g x) (abs_nonneg β)

lemma integrable_partition (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α (N + 1)) :
    Integrable (fun x => Real.exp (β * hamiltonian α φ (N + 1) g x))
      (sphereLaw (N + 1)) := by
  apply (integrable_const (Real.exp (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖))).mono'
  · exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_hamiltonian α φ (N + 1)).comp
        (continuous_const.prodMk continuous_id)))).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_exp.mpr ((abs_le.mp (abs_energy_le α β φ (N + 1) g x)).2)

lemma partition_bounds (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α (N + 1)) :
    Real.exp (- (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖)) ≤
      (∫ x, Real.exp (β * hamiltonian α φ (N + 1) g x) ∂sphereLaw (N + 1)) ∧
    (∫ x, Real.exp (β * hamiltonian α φ (N + 1) g x) ∂sphereLaw (N + 1)) ≤
      Real.exp (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖) := by
  constructor
  · calc
      _ = ∫ _ : Spin (N + 1), Real.exp (- (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖))
          ∂sphereLaw (N + 1) := by simp
      _ ≤ _ := integral_mono (integrable_const _) (integrable_partition α β φ N g)
        (fun x => Real.exp_le_exp.mpr ((abs_le.mp (abs_energy_le α β φ (N + 1) g x)).1))
  · calc
      _ ≤ ∫ _ : Spin (N + 1), Real.exp (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖)
          ∂sphereLaw (N + 1) := integral_mono (integrable_partition α β φ N g)
        (integrable_const _)
        (fun x => Real.exp_le_exp.mpr ((abs_le.mp (abs_energy_le α β φ (N + 1) g x)).2))
      _ = _ := by simp

lemma partition_pos (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α (N + 1)) :
    0 < ∫ x, Real.exp (β * hamiltonian α φ (N + 1) g x) ∂sphereLaw (N + 1) :=
  (Real.exp_pos _).trans_le (partition_bounds α β φ N g).1

lemma continuous_partition (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    Continuous (fun g : Patterns α (N + 1) =>
      ∫ x, Real.exp (β * hamiltonian α φ (N + 1) g x) ∂sphereLaw (N + 1)) := by
  apply continuous_of_dominated (bound := fun _ =>
    Real.exp (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖))
  · intro g
    exact (integrable_partition α β φ N g).aestronglyMeasurable
  · intro g
    apply Filter.Eventually.of_forall
    intro x
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_exp.mpr ((abs_le.mp (abs_energy_le α β φ (N + 1) g x)).2)
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro x
    exact Real.continuous_exp.comp (continuous_const.mul
      ((continuous_hamiltonian α φ (N + 1)).comp
        (continuous_id.prodMk continuous_const)))

lemma continuous_pressure (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    Continuous (pressure α β φ (N + 1)) := by
  unfold pressure
  apply Continuous.div_const
  exact (continuous_partition α β φ N).log (fun g => ne_of_gt (partition_pos α β φ N g))

lemma abs_pressure_le (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α (N + 1)) :
    |pressure α β φ (N + 1) g| ≤
      |β| * (patternCount α (N + 1) : ℝ) * ‖φ‖ / (N + 1 : ℝ) := by
  have hp := partition_pos α β φ N g
  have hb := partition_bounds α β φ N g
  have hlo := Real.log_le_log (Real.exp_pos _) hb.1
  have hhi := Real.log_le_log hp hb.2
  rw [Real.log_exp] at hlo hhi
  have hd : 0 ≤ (N + 1 : ℝ) := by positivity
  unfold pressure
  rw [abs_div, abs_of_nonneg (show 0 ≤ ((N + 1 : ℕ) : ℝ) by positivity)]
  simpa only [Nat.cast_add, Nat.cast_one] using div_le_div_of_nonneg_right
    (abs_le.mpr ⟨hlo, hhi⟩) hd

lemma integrable_pressure (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    Integrable (pressure α β φ (N + 1)) (patternLaw α (N + 1)) := by
  exact (integrable_const _).mono' (continuous_pressure α β φ N).aestronglyMeasurable
    (Filter.Eventually.of_forall (abs_pressure_le α β φ N))

end SphericalPerceptron
end
end

end OAI
