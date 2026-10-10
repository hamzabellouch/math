import Mathlib
import OAI.Probability.SKGap.Terminal.FiniteSpinCalculus
import OAI.Probability.SKGap.Gaussian.StandardGaussianProduct

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
namespace SKGap
open scoped BigOperators

lemma gaussian_integrable_pow (k : ℕ) :
    Integrable (fun x : ℝ => x^k) (gaussianReal 0 1) := by
  apply (integrable_norm_iff (by fun_prop)).mp
  simpa only [id_eq, norm_pow] using
    (IsGaussian.memLp_id (gaussianReal 0 1) (k : ℝ≥0∞) (by simp)).integrable_norm_pow'

lemma gaussian_memLp_sq : MemLp (fun x : ℝ => x^2) 2 (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [← pow_mul] using gaussian_integrable_pow 4

lemma gaussian_integral_sq : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop), integral_id_gaussianReal] at h
  simpa only [sub_zero, NNReal.coe_one] using h

lemma gaussian_integral_fourth : (∫ x : ℝ, x^4 ∂gaussianReal 0 1) = 3 := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => x^3) (3*x^2) x := by
    convert! (hasDerivAt_id x).pow 3 using 1; norm_num [Pi.pow_apply, id_eq]
  have hi : Integrable (fun x : ℝ => (x - 0)*x^3) (gaussianReal 0 1) := by
    simpa only [sub_zero, ← pow_succ'] using gaussian_integrable_pow 4
  have h := gaussian_integration_by_parts (by norm_num : (1 : ℝ≥0) ≠ 0)
    hd (gaussian_integrable_pow 3) ((gaussian_integrable_pow 2).const_mul 3) hi
  simpa only [sub_zero, ← pow_succ', integral_const_mul, gaussian_integral_sq,
    NNReal.coe_one, one_mul, mul_one] using h

lemma gaussian_variance_sq : Var[fun x : ℝ => x^2; gaussianReal 0 1] = 2 := by
  rw [variance_eq_sub gaussian_memLp_sq]
  simp only [Pi.pow_apply, ← pow_mul, gaussian_integral_fourth, gaussian_integral_sq]
  norm_num

section Quadratic
variable {ι : Type*} [Fintype ι]

def gaussianQuadratic (a : ι → ℝ) (x : ι → ℝ) : ℝ := ∑ i, a i * (x i)^2

lemma gaussianQuadratic_memLp (a : ι → ℝ) :
    MemLp (gaussianQuadratic a) 2 (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  apply memLp_finsetSum
  intro i _
  exact ((gaussian_memLp_sq.const_mul (a i)).comp_measurePreserving
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i))

lemma gaussianQuadratic_mean (a : ι → ℝ) :
    (∫ x, gaussianQuadratic a x ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = ∑ i, a i := by
  unfold gaussianQuadratic
  have hi (i : ι) : Integrable (fun x : ι → ℝ => a i * (x i)^2)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    ((gaussian_memLp_sq.const_mul (a i)).comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i)).integrable (by norm_num)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  have he : (∫ x : ι → ℝ, (x i)^2 ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∫ y : ℝ, y^2 ∂gaussianReal 0 1 :=
    integral_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := i)
      (f := fun y : ℝ => y^2) (by fun_prop)
  rw [he, gaussian_integral_sq, mul_one]

lemma gaussianQuadratic_variance (a : ι → ℝ) :
    Var[gaussianQuadratic a; Measure.pi (fun _ : ι => gaussianReal 0 1)] =
      2 * ∑ i, (a i)^2 := by
  have h : Var[gaussianQuadratic a; Measure.pi (fun _ : ι => gaussianReal 0 1)] =
      ∑ i, Var[fun x : ℝ => a i * x^2; gaussianReal 0 1] := by
    convert variance_sum_pi (fun i : ι => gaussian_memLp_sq.const_mul (a i)) using 1
    congr 1
    funext x
    simp only [gaussianQuadratic, Finset.sum_apply]
  rw [h]
  simp only [variance_const_mul, gaussian_variance_sq, ← Finset.sum_mul]
  ring

end Quadratic

lemma sqrt_sub_sq_le_abs_sub {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (sqrt x - sqrt y)^2 ≤ |x-y| := by
  have hx2 := sq_sqrt hx
  have hy2 := sq_sqrt hy
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hh := sqrt_le_sqrt h
    nlinarith [mul_nonneg (sqrt_nonneg x) (sub_nonneg.mpr hh)]
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hh := sqrt_le_sqrt h
    nlinarith [mul_nonneg (sqrt_nonneg y) (sub_nonneg.mpr hh)]

section Fluctuation
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma memLp_sqrt_of_nonneg {f : Ω → ℝ} (hf : Integrable f μ)
    (hpos : ∀ x, 0 ≤ f x) : MemLp (fun x => sqrt (f x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)).mpr
  exact hf.congr (Filter.Eventually.of_forall (fun x => (sq_sqrt (hpos x)).symm))

lemma integral_abs_le_sqrt_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ sqrt (∫ x, (f x)^2 ∂μ) := by
  have h0 := ProbabilityTheory.variance_nonneg (fun x => ‖f x‖) μ
  rw [variance_eq_sub hf.norm] at h0
  have hsq : (∫ x, |f x| ∂μ)^2 ≤ ∫ x, (f x)^2 ∂μ := by
    simpa only [Real.norm_eq_abs, Pi.pow_apply, sq_abs, sub_nonneg] using h0
  have hi : 0 ≤ ∫ x, (f x)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hh := sq_sqrt hi
  have hp := sqrt_nonneg (∫ x, (f x)^2 ∂μ)
  nlinarith [sq_nonneg ((∫ x, |f x| ∂μ) - sqrt (∫ x, (f x)^2 ∂μ))]

theorem integral_sqrt_fluctuation {f : Ω → ℝ} (hf : MemLp f 2 μ)
    (hpos : ∀ x, 0 ≤ f x) :
    (∫ x, |sqrt (f x) - sqrt (∫ y, f y ∂μ)| ∂μ) ≤ sqrt (sqrt (Var[f; μ])) := by
  let m := ∫ y, f y ∂μ
  have hm : 0 ≤ m := integral_nonneg hpos
  have hg : MemLp (fun x => f x - m) 2 μ := hf.sub (memLp_const m)
  have hroot : MemLp (fun x => sqrt (f x) - sqrt m) 2 μ := by
    apply (memLp_two_iff_integrable_sq ((Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable).sub aestronglyMeasurable_const)).mpr
    apply hg.integrable (by norm_num) |>.norm |>.mono'
      (((Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable).sub aestronglyMeasurable_const).pow 2)
    filter_upwards [] with x
    change |(sqrt (f x) - sqrt m)^2| ≤ |f x - m|
    rw [abs_of_nonneg (sq_nonneg (sqrt (f x) - sqrt m))]
    exact sqrt_sub_sq_le_abs_sub (hpos x) hm
  have hdiff : (∫ x, (sqrt (f x) - sqrt m)^2 ∂μ) ≤ ∫ x, |f x-m| ∂μ := by
    apply integral_mono hroot.integrable_sq (hg.integrable (by norm_num)).norm
    exact fun x => sqrt_sub_sq_le_abs_sub (hpos x) hm
  have hc := integral_abs_le_sqrt_sq hg
  rw [← variance_eq_integral hf.aemeasurable] at hc
  exact (integral_abs_le_sqrt_sq hroot).trans (sqrt_le_sqrt (hdiff.trans hc))

end Fluctuation
end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
