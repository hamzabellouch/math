import Mathlib
import OAI.Probability.SphericalField.Gaussian.Taylor

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
def gaussianAverage (s : ℝ≥0) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, f (x + z) ∂gaussianReal 0 s

lemma gaussianAverage_integrable (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    Integrable (fun z => f (x + z)) (gaussianReal 0 s) :=
  boundedContinuousFunction_integrable_comp f (by fun_prop)

lemma gaussianAverage_abs_le (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    |gaussianAverage s f x| ≤ ‖f‖ := by
  simpa [gaussianAverage, Real.norm_eq_abs] using
    norm_integral_le_of_norm_le_const (μ := gaussianReal 0 s)
      (Filter.Eventually.of_forall fun z => f.norm_coe_le_norm (x+z))

lemma gaussianAverage_continuous (s : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    Continuous (gaussianAverage s f) := by
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro x; exact (gaussianAverage_integrable s f x).aestronglyMeasurable
  · intro x; exact Filter.Eventually.of_forall fun z => f.norm_coe_le_norm (x+z)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun z => f.continuous.comp (continuous_id.add continuous_const)

def gaussianAverageBCF (s : ℝ≥0) (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨gaussianAverage s f, gaussianAverage_continuous s f⟩
    (2*‖f‖) (by
      intro x y
      change |gaussianAverage s f x - gaussianAverage s f y| ≤ 2 * ‖f‖
      exact (abs_sub _ _).trans (by linarith [gaussianAverage_abs_le s f x, gaussianAverage_abs_le s f y]))

@[simp] lemma gaussianAverageBCF_coe (s : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    (gaussianAverageBCF s f : ℝ → ℝ) = gaussianAverage s f := rfl

@[simp] lemma gaussianAverage_zero (f : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage 0 f x = f x := by simp [gaussianAverage]

lemma gaussianAverage_semigroup (s t : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage s (gaussianAverageBCF t f) x = gaussianAverage (s+t) f x := by
  have hi : Integrable (fun z => f (x+z)) ((gaussianReal 0 s) ∗ (gaussianReal 0 t)) := by
    rw [gaussianReal_conv_gaussianReal, zero_add]
    exact gaussianAverage_integrable (s+t) f x
  have hh := integral_conv hi
  simp only [gaussianReal_conv_gaussianReal, zero_add] at hh
  simpa only [gaussianAverage, gaussianAverageBCF_coe, add_assoc] using hh.symm

lemma gaussianAverage_hasDerivAt (s : ℝ≥0) (f f' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f : ℝ → ℝ) (f' x) x) (x : ℝ) :
    HasDerivAt (gaussianAverage s f) (gaussianAverage s f' x) x := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (F := fun x z => f (x+z)) (F' := fun x z => f' (x+z)) (bound := fun _ => ‖f'‖)
    (μ := gaussianReal 0 s) (by simp)
    (Filter.Eventually.of_forall fun x => (gaussianAverage_integrable s f x).aestronglyMeasurable)
    (gaussianAverage_integrable s f x)
    (gaussianAverage_integrable s f' x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z x _ => f'.norm_coe_le_norm (x+z)) (integrable_const _)
    (Filter.Eventually.of_forall fun z x _ => by convert! (hf (x+z)).comp x ((hasDerivAt_id x).add_const z) using 1; simp only [mul_one])).2

lemma gaussianAverage_deriv (s : ℝ≥0) (f f' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f : ℝ → ℝ) (f' x) x) :
    deriv (gaussianAverage s f) = gaussianAverage s f' := by
  funext x; exact (gaussianAverage_hasDerivAt s f f' hf x).deriv

lemma exp_bcf_bound (d : ℝ) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    |Real.exp (d * f x)| ≤ Real.exp (|d| * ‖f‖) := by
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    d * f x ≤ |d * f x| := le_abs_self _
    _ = |d| * |f x| := abs_mul _ _
    _ ≤ |d| * ‖f‖ := mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x) (abs_nonneg d)

def expBCF (d : ℝ) (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => Real.exp (d*f x), by fun_prop⟩
    (2 * Real.exp (|d| * ‖f‖)) (by
      intro x y; change |Real.exp (d * f x) - Real.exp (d * f y)| ≤ 2 * Real.exp (|d| * ‖f‖)
      exact (abs_sub _ _).trans (by linarith [exp_bcf_bound d f x, exp_bcf_bound d f y]))

@[simp] lemma expBCF_apply (d : ℝ) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    expBCF d f x = Real.exp (d * f x) := rfl

lemma gaussianAverage_exp_pos (s : ℝ≥0) (d : ℝ) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    0 < gaussianAverage s (expBCF d f) x := by
  apply integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos (d*f (x+z))).le)
    (gaussianAverage_integrable s (expBCF d f) x) |>.mpr
  simpa only [Function.support, expBCF_apply, ne_eq, Real.exp_ne_zero, not_false_eq_true,
    Set.ofPred_true, measure_univ] using (zero_lt_one : (0 : ℝ≥0∞) < 1)

lemma gaussianAverage_exp_bounds (s : ℝ≥0) (d : ℝ) (hd : 0 ≤ d) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    Real.exp (-d*‖f‖) ≤ gaussianAverage s (expBCF d f) x ∧
      gaussianAverage s (expBCF d f) x ≤ Real.exp (d*‖f‖) := by
  have hf : ∀ z, |f (x+z)| ≤ ‖f‖ := fun z => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (x+z)
  constructor
  · have hi := integral_mono (integrable_const (Real.exp (-d*‖f‖)))
      (gaussianAverage_integrable s (expBCF d f) x) (fun z =>
        Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp (hf z)).1]))
    simpa only [gaussianAverage, integral_const, probReal_univ, smul_eq_mul, one_mul] using hi
  · have hi := integral_mono (gaussianAverage_integrable s (expBCF d f) x)
      (integrable_const (Real.exp (d*‖f‖))) (fun z =>
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hf z)).2 hd))
    simpa only [gaussianAverage, integral_const, probReal_univ, smul_eq_mul, one_mul] using hi

end SphericalPerceptron
end
end

end OAI
