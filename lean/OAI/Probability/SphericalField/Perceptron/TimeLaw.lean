import Mathlib
import OAI.Probability.SphericalField.Perceptron.Model

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
instance (α : ℝ) (N : ℕ) : IsProbabilityMeasure (patternLaw α N) := by
  unfold patternLaw
  infer_instance

instance : NullSingletonClass timeLaw := by
  rw [timeLaw_eq_volume]
  infer_instance

theorem progressive_zero (P : Measure BrownianPath) :
    Progressive P (fun _ _ => 0) := by
  intro t
  exact measurable_const

@[simp] theorem controlCost_zero (P : Measure BrownianPath) (m : Trial) :
    controlCost P m (fun _ _ => 0) = 0 := by
  simp [controlCost]

@[simp] theorem controlPayoff_zero (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (m : Trial) :
    controlPayoff P f m (fun _ _ => 0) = ∫ ω, f (brownianEval 1 ω) ∂P := by
  simp [controlPayoff]

theorem abs_integral_reward_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (X : BrownianPath → ℝ) :
    |∫ ω, f (X ω) ∂P| ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const
    (μ := P) (f := fun ω => f (X ω)) (C := ‖f‖)
    (Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm (X ω))
  simpa using h

theorem controlPayoff_le_norm (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (v : Time → BrownianPath → ℝ) :
    controlPayoff P f m v ≤ ‖f‖ := by
  unfold controlPayoff
  have h := (abs_integral_reward_le P f
    (fun ω => brownianEval 1 ω + ∫ t, m t * v t ω ∂timeLaw))
  have h := (le_abs_self _).trans h
  exact (sub_le_self _ (div_nonneg ENNReal.toReal_nonneg (by norm_num))).trans h

theorem controlPayoffs_nonempty (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (m : Trial) :
    {a | ∃ v : Time → BrownianPath → ℝ,
      Progressive P v ∧ controlCost P m v < ∞ ∧ a = controlPayoff P f m v}.Nonempty := by
  exact ⟨_, fun _ _ => 0, progressive_zero P, by simp, rfl⟩

theorem controlPayoffs_bddAbove (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) :
    BddAbove {a | ∃ v : Time → BrownianPath → ℝ,
      Progressive P v ∧ controlCost P m v < ∞ ∧ a = controlPayoff P f m v} := by
  refine ⟨‖f‖, ?_⟩
  rintro a ⟨v, _, _, rfl⟩
  exact controlPayoff_le_norm P f m v

theorem controlValue_le_norm (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) : controlValue P f m ≤ ‖f‖ := by
  apply csSup_le (controlPayoffs_nonempty P f m)
  rintro a ⟨v, _, _, rfl⟩
  exact controlPayoff_le_norm P f m v

theorem zero_payoff_le_controlValue (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) :
    (∫ ω, f (brownianEval 1 ω) ∂P) ≤ controlValue P f m := by
  apply le_csSup (controlPayoffs_bddAbove P f m)
  exact ⟨fun _ _ => 0, progressive_zero P, by simp, by simp⟩

theorem neg_norm_le_controlValue (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) : -‖f‖ ≤ controlValue P f m := by
  exact (abs_le.mp (abs_integral_reward_le P f (brownianEval 1))).1.trans
    (zero_payoff_le_controlValue P f m)

theorem abs_controlValue_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) : |controlValue P f m| ≤ ‖f‖ := by
  exact abs_le.mpr ⟨neg_norm_le_controlValue P f m, controlValue_le_norm P f m⟩

def oneTrial : Trial where
  toFun := fun _ => 1
  monotone := monotone_const
  measurable := measurable_const
  nonneg := fun _ => zero_le_one
  le_one := fun _ => le_rfl

@[simp] theorem oneTrial_apply (t : Time) : oneTrial t = 1 := rfl

@[simp] theorem tailIntegral_oneTrial (t : Time) :
    tailIntegral oneTrial t = 1 - (t : ℝ) := by
  simp [tailIntegral, Measure.real, ENNReal.toReal_ofReal, sub_nonneg.mpr t.2.2]

@[simp] theorem entropy_oneTrial : entropy oneTrial = 0 := by
  simp [entropy]

instance (N : ℕ) : IsProbabilityMeasure (unitSphereLaw (N + 1)) := by
  have : NeZero ((volume : Measure (Spin (N + 1))).toSphere) :=
    ⟨Measure.toSphere_ne_zero volume⟩
  unfold unitSphereLaw
  infer_instance

instance (N : ℕ) : IsProbabilityMeasure (sphereLaw (N + 1)) := by
  unfold sphereLaw
  apply (Measure.isProbabilityMeasure_map_iff ?_).2 inferInstance
  exact ((continuous_const : Continuous (fun _ : Metric.sphere (0 : Spin (N+1)) 1 =>
    Real.sqrt (N+1 : ℕ))).smul
    (continuous_subtype_val : Continuous (fun x : Metric.sphere (0 : Spin (N+1)) 1 => x.val))).measurable.aemeasurable

lemma continuous_patternField {α : ℝ} {N : ℕ} (a : Fin (patternCount α N)) :
    Continuous (fun p : Patterns α N × Spin N => patternField p.1 a p.2) := by
  unfold patternField
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp ((continuous_apply a).comp
    (continuous_fst : Continuous (fun p : Patterns α N × Spin N => p.1)))).mul
    ((EuclideanSpace.proj i).continuous.comp
      (continuous_snd : Continuous (fun p : Patterns α N × Spin N => p.2)))

lemma continuous_hamiltonian (α : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    Continuous (fun p : Patterns α N × Spin N => hamiltonian α φ N p.1 p.2) := by
  unfold hamiltonian
  apply continuous_finsetSum
  intro a _
  exact φ.continuous.comp (continuous_patternField a)

lemma abs_hamiltonian_le (α : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α N) (x : Spin N) :
    |hamiltonian α φ N g x| ≤ (patternCount α N : ℝ) * ‖φ‖ := by
  unfold hamiltonian
  calc
    |∑ a, φ (patternField g a x)| ≤ ∑ a, |φ (patternField g a x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin (patternCount α N), ‖φ‖ :=
      Finset.sum_le_sum fun a _ => φ.norm_coe_le_norm _
    _ = _ := by simp

end SphericalPerceptron
end
end

end OAI
