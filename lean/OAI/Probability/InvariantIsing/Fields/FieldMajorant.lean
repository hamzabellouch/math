import OAI.Probability.InvariantIsing.Fields.Field
import OAI.Probability.IsingPerceptron.VariationalDefs
import OAI.Probability.IsingPerceptron.ConvexDerivativeFluctuation
import Mathlib.Analysis.MeanInequalitiesPow

namespace OAI

/-!
# The entropy-domain majorant

The explicit majorant in Lemma `fld:domain` of Section 2 is unbounded but has
linear growth.  Its Gaussian bounds follow from exponential moments.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace InvariantIsing

/-- The function `g_d` used for the finite entropy-domain estimate. -/
def fieldMajorant (d z : ℝ) : ℝ :=
  Real.log (Real.exp (d * z) + Real.exp (-d * z)) / d - Real.log 2

lemma exp_add_exp_neg_eq_two_cosh (z : ℝ) :
    Real.exp z + Real.exp (-z) = 2 * Real.cosh z := by
  rw [Real.cosh_eq]
  ring

lemma fieldMajorant_eq_logcosh {d : ℝ} (hd : d ≠ 0) (z : ℝ) :
    fieldMajorant d z = Real.log (Real.cosh (d * z)) / d +
      (d⁻¹ - 1) * Real.log 2 := by
  rw [fieldMajorant, show -d * z = -(d * z) by ring,
    exp_add_exp_neg_eq_two_cosh,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.cosh_pos _).ne']
  field_simp
  ring

@[simp] lemma fieldMajorant_zero (d : ℝ) :
    fieldMajorant d 0 = (d⁻¹ - 1) * Real.log 2 := by
  simp only [fieldMajorant, mul_zero, Real.exp_zero, one_add_one_eq_two]
  ring

lemma measurable_fieldMajorant (d : ℝ) : Measurable (fieldMajorant d) := by
  unfold fieldMajorant
  fun_prop

lemma fieldMajorant_linearGrowth {d : ℝ} (hd : 0 < d) :
    IsingPerceptron.HasLinearGrowth (fieldMajorant d) := by
  refine ⟨|(d⁻¹ - 1) * Real.log 2|, 1, abs_nonneg _, zero_le_one, fun z => ?_⟩
  rw [fieldMajorant_eq_logcosh hd.ne']
  have hb : |Real.log (Real.cosh (d * z)) / d| ≤ |z| := by
    rw [abs_div, abs_of_pos hd]
    apply (div_le_iff₀ hd).2
    have h := IsingPerceptron.abs_log_cosh_le (d * z)
    simpa only [abs_mul, abs_of_pos hd, mul_comm] using h
  simpa only [one_mul, Real.norm_eq_abs, add_comm] using
    (abs_add_le (Real.log (Real.cosh (d * z)) / d) ((d⁻¹ - 1) * Real.log 2)).trans
      (add_le_add hb le_rfl)

/-- The terminal Ising payoff lies below `g_d` when `d ≤ 1`. -/
lemma logcosh_le_fieldMajorant {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (z : ℝ) :
    Real.log (Real.cosh z) ≤ fieldMajorant d z := by
  have hpow := Real.add_rpow_le_rpow_add
    (Real.exp_pos (d * z)).le (Real.exp_pos (-d * z)).le
    (show 1 ≤ d⁻¹ by exact (one_le_inv₀ hd).2 hd1)
  have h₁ : Real.exp (d * z) ^ d⁻¹ = Real.exp z := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  have h₂ : Real.exp (-d * z) ^ d⁻¹ = Real.exp (-z) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  rw [h₁, h₂] at hpow
  have hl := Real.log_le_log (add_pos (Real.exp_pos z) (Real.exp_pos (-z))) hpow
  rw [Real.log_rpow (add_pos (Real.exp_pos _) (Real.exp_pos _))] at hl
  rw [exp_add_exp_neg_eq_two_cosh,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.cosh_pos z).ne'] at hl
  unfold fieldMajorant
  rw [div_eq_mul_inv]
  linarith

/-- A two-point convexity inequality.  Its weights are the two terms of the
partition function at the unshifted field. -/
lemma weighted_exp_log_sum_le {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    {p : ℝ} (hp : 1 ≤ p) (x : ℝ) :
    Real.exp (p * Real.log ((A * Real.exp x + B * Real.exp (-x)) / (A + B))) ≤
      (A / (A + B)) * Real.exp (p * x) +
        (B / (A + B)) * Real.exp (-p * x) := by
  have hAB : 0 < A + B := add_pos hA hB
  have hw : A / (A + B) + B / (A + B) = 1 := by
    rw [← add_div, div_self hAB.ne']
  have hc := (convexOn_rpow hp).2
    (show Real.exp x ∈ Ici (0 : ℝ) from (Real.exp_pos _).le)
    (show Real.exp (-x) ∈ Ici (0 : ℝ) from (Real.exp_pos _).le)
    (div_nonneg hA.le hAB.le) (div_nonneg hB.le hAB.le) hw
  simp only [smul_eq_mul] at hc
  have hn : A / (A + B) * Real.exp x + B / (A + B) * Real.exp (-x) =
      (A * Real.exp x + B * Real.exp (-x)) / (A + B) := by ring
  rw [hn] at hc
  rw [Real.rpow_def_of_pos (div_pos
    (add_pos (mul_pos hA (Real.exp_pos _)) (mul_pos hB (Real.exp_pos _))) hAB),
    ← Real.exp_mul, ← Real.exp_mul] at hc
  convert hc using 1 <;> congr 1 <;> ring_nf

lemma fieldMajorant_increment_eq {d : ℝ} (_hd : d ≠ 0) (z q : ℝ) :
    fieldMajorant d (z + q) - fieldMajorant d z =
      Real.log ((Real.exp (d * z) * Real.exp (d * q) +
        Real.exp (-d * z) * Real.exp (-d * q)) /
        (Real.exp (d * z) + Real.exp (-d * z))) / d := by
  rw [Real.log_div (by positivity :
    Real.exp (d * z) * Real.exp (d * q) +
      Real.exp (-d * z) * Real.exp (-d * q) ≠ 0)
    (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne']
  simp only [fieldMajorant, mul_add, Real.exp_add]
  ring

/-- The sharp Gaussian exponential-moment bound in the branch `a ≥ d`. -/
lemma fieldMajorant_increment_exp_le {d a : ℝ} (hd : 0 < d) (hda : d ≤ a)
    (z q : ℝ) :
    Real.exp (a * (fieldMajorant d (z + q) - fieldMajorant d z)) ≤
      (Real.exp (d * z) / (Real.exp (d * z) + Real.exp (-d * z))) * Real.exp (a * q) +
      (Real.exp (-d * z) / (Real.exp (d * z) + Real.exp (-d * z))) * Real.exp (-a * q) := by
  have hp : 1 ≤ a / d := (le_div_iff₀ hd).2 (by simpa using hda)
  have h := weighted_exp_log_sum_le (Real.exp_pos (d * z))
    (Real.exp_pos (-d * z)) hp (d * q)
  rw [fieldMajorant_increment_eq hd.ne']
  convert h using 1 <;> congr 1 <;> field_simp

/-- Exponential integrability of every shifted majorant, needed throughout the
finite backward recursion. -/
lemma integrable_exp_fieldMajorant {d : ℝ} (hd : 0 < d) (z s a : ℝ) :
    Integrable (fun y : ℝ => Real.exp (a * fieldMajorant d (z + s * y)))
      (gaussianReal 0 1) :=
  IsingPerceptron.integrable_exp_of_linearGrowth _
    (IsingPerceptron.gaussianReal_exponentialNormMoments _ _)
    ((measurable_fieldMajorant d).comp (measurable_const.add (measurable_id.const_mul _)))
    (((fieldMajorant_linearGrowth hd).add_left z).scale_argument s) a

end InvariantIsing

end

end OAI
