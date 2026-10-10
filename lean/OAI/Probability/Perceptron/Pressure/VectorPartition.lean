import Mathlib
import OAI.Probability.Perceptron.Sphere.GaussianRotation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {S : Type*} [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]
  {W : S → ℝ} {V : S → StrongDual ℝ E}

def vectorPartition (W : S → ℝ) (V : S → StrongDual ℝ E) (x : E) : ℝ :=
  ∫ s, Real.exp (W s + V s x) ∂ρ

def vectorLogPartition (W : S → ℝ) (V : S → StrongDual ℝ E) (x : E) : ℝ :=
  Real.log (vectorPartition ρ W V x)

def vectorLogDerivative (W : S → ℝ) (V : S → StrongDual ℝ E) (x : E) : StrongDual ℝ E :=
  (vectorPartition ρ W V x)⁻¹ • (∫ s, Real.exp (W s + V s x) • V s ∂ρ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace S] in
lemma vectorEnergy_bound {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C)
    (x : E) (s : S) : |W s + V s x| ≤ K+C*‖x‖ := by
  apply (abs_add_le _ _).trans
  apply add_le_add (hW s)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hV s) (norm_nonneg x))

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorPartition_integrable (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    Integrable (fun s => Real.exp (W s + V s x)) ρ := by
  refine Integrable.of_bound (by fun_prop) (Real.exp (K+C*‖x‖)) (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (vectorEnergy_bound hW hV x s))

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorPartition_pos (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    0 < vectorPartition ρ W V x := by
  apply integral_pos_iff_support_of_nonneg (fun s => (Real.exp_pos _).le)
    (vectorPartition_integrable ρ hWm hVm hW hV x) |>.mpr
  simp [Function.support,Real.exp_ne_zero]

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorPartition_hasFDerivAt (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hC : 0 ≤ C) (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    HasFDerivAt (vectorPartition ρ W V) (∫ s, Real.exp (W s+V s x) • V s ∂ρ) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball x 1) (bound := fun _ => Real.exp (K+C*(‖x‖+1))*C)
    (F' := fun y s => Real.exp (W s+V s y) • V s) (Metric.ball_mem_nhds x zero_lt_one)
    (Filter.Eventually.of_forall fun y => by fun_prop)
    (vectorPartition_integrable ρ hWm hVm hW hV x) (by fun_prop)
    (ae_of_all _ fun s y hy => ?_) (integrable_const _) (ae_of_all _ fun s y _ => ?_)
  · have hy' : ‖y‖ ≤ ‖x‖+1 := by
      have hh : ‖y-x‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
      have hn := norm_add_le (y-x) x
      rw [sub_add_cancel] at hn
      linarith
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul _ (hV _) (norm_nonneg _) (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    exact ((le_abs_self _).trans (vectorEnergy_bound hW hV y s)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' hC))
  · exact (((V s).hasFDerivAt).const_add (W s)).exp

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogPartition_hasFDerivAt (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hC : 0 ≤ C) (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    HasFDerivAt (vectorLogPartition ρ W V) (vectorLogDerivative ρ W V x) x :=
  (vectorPartition_hasFDerivAt ρ hWm hVm hC hW hV x).log
    (vectorPartition_pos ρ hWm hVm hW hV x).ne'

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogDerivative_bound (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    ‖vectorLogDerivative ρ W V x‖ ≤ C := by
  have hp := vectorPartition_pos ρ hWm hVm hW hV x
  have hn : ‖∫ s, Real.exp (W s+V s x) • V s ∂ρ‖ ≤ C*vectorPartition ρ W V x := by
    have hh := norm_integral_le_of_norm_le (f := fun s => Real.exp (W s+V s x) • V s)
      ((vectorPartition_integrable ρ hWm hVm hW hV x).const_mul C)
      (ae_of_all _ fun s => by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact (mul_le_mul_of_nonneg_left (hV s) (Real.exp_pos _).le).trans_eq (mul_comm ..))
    simpa only [integral_const_mul,vectorPartition] using hh
  rw [vectorLogDerivative,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
  calc
    _ ≤ (vectorPartition ρ W V x)⁻¹*(C*vectorPartition ρ W V x) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hp.le)
    _ = C := by field_simp

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogDerivative_continuous (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hC : 0 ≤ C) (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) :
    Continuous (vectorLogDerivative ρ W V) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hp := (vectorPartition_hasFDerivAt ρ hWm hVm hC hW hV x).continuousAt
  apply (hp.inv₀ (vectorPartition_pos ρ hWm hVm hW hV x).ne').smul
  apply continuousAt_of_dominated (bound := fun _ => Real.exp (K+C*(‖x‖+1))*C)
  · exact Filter.Eventually.of_forall fun y => by fun_prop
  · filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
    exact ae_of_all _ fun s => by
      have hy' : ‖y‖ ≤ ‖x‖+1 := by
        have hh : ‖y-x‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
        have hn := norm_add_le (y-x) x
        rw [sub_add_cancel] at hn
        linarith
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul _ (hV _) (norm_nonneg _) (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      exact ((le_abs_self _).trans (vectorEnergy_bound hW hV y s)).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' hC))
  · exact integrable_const _
  · exact ae_of_all _ fun s => by fun_prop

lemma vectorLogPartition_gaussian_variance (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hC : 0 ≤ C) (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) :
    variance (vectorLogPartition ρ W V) (stdGaussian E) ≤ (Real.pi^2/8)*C^2 :=
  stdGaussian_variance_le_of_fderiv_bound
    (vectorLogPartition_hasFDerivAt ρ hWm hVm hC hW hV)
    (vectorLogDerivative_continuous ρ hWm hVm hC hW hV) hC
    (vectorLogDerivative_bound ρ hWm hVm hW hV)

end SphericalPerceptronFreeEnergy

end

end OAI
