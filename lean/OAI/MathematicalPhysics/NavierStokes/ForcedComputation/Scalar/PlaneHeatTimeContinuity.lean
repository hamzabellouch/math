import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatOperator
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetKernelDependence

namespace OAI

/-! Operator-norm continuity of Gaussian heat operators at every strictly positive time. -/

noncomputable section
namespace ForcedComputation.PlaneHeat

open Real MeasureTheory Set Filter ShearFlows
open scoped Topology ContDiff

def timeCore (b y : ℝ) : ℝ := Real.exp (-(4 * b)⁻¹ * y ^ 2)
def timeCoefficient (a : ℝ) : ℝ := (Real.sqrt (4 * Real.pi * a))⁻¹
def timeEnvelope (a b : ℝ) (y : Plane) : ℝ :=
  timeCoefficient a ^ 2 * (timeCore b (y 0) * timeCore b (y 1))
private def timeDerivativeEnvelope (a b : ℝ) (j : Fin 2) (y : Plane) : ℝ :=
  (|y j| / (2 * a)) * timeEnvelope a b y

theorem oneDim_time_le {a b s : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    (y : ℝ) : oneDim s y ≤ timeCoefficient a * timeCore b y := by
  have hs : 0 < s := ha.trans_le has
  have hn : (Real.sqrt (4 * Real.pi * s))⁻¹ ≤ timeCoefficient a := by
    unfold timeCoefficient
    simpa only [one_div] using (show (1 / Real.sqrt (4 * Real.pi * s)) ≤
      1 / Real.sqrt (4 * Real.pi * a) from
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity))
        (Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])))
  have hi : (4 * b)⁻¹ ≤ (4 * s)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (by positivity : 0 < 4 * s) (by linarith : 4 * s ≤ 4 * b)
  have he : -(4 * s)⁻¹ * y ^ 2 ≤ -(4 * b)⁻¹ * y ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hi (sq_nonneg y)]
  exact mul_le_mul hn (Real.exp_le_exp.mpr he) (le_of_lt (Real.exp_pos _))
    (by unfold timeCoefficient; positivity)

theorem kernel_time_le {a b s : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    (y : Plane) : kernel s y ≤ timeEnvelope a b y := by
  have h0 := oneDim_time_le ha has hsb (y 0)
  have h1 := oneDim_time_le ha has hsb (y 1)
  calc
    _ ≤ (timeCoefficient a * timeCore b (y 0)) *
          (timeCoefficient a * timeCore b (y 1)) :=
      mul_le_mul h0 h1 (oneDim_nonneg _ _) ((oneDim_nonneg _ _).trans h0)
    _ = _ := by unfold timeEnvelope; ring

private theorem derivative_time_le {a b s : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    (j : Fin 2) (y : Plane) : |kernelDerivative s j y| ≤ timeDerivativeEnvelope a b j y := by
  have hs : 0 < s := ha.trans_le has
  rw [kernelDerivative, abs_mul, abs_neg, abs_div, abs_of_pos (by positivity : 0 < 2 * s),
    abs_of_nonneg (kernel_nonneg _ _)]
  exact mul_le_mul
    (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by linarith : 2 * a ≤ 2 * s))
    (kernel_time_le ha has hsb y) (kernel_nonneg _ _) (by positivity)

theorem timeCore_integrable {b : ℝ} (hb : 0 < b) : Integrable (timeCore b) :=
  integrable_exp_neg_mul_sq (by positivity)

private theorem timeMoment_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : ℝ => |y| * timeCore b y) := by
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), timeCore] using
    (integrable_mul_exp_neg_mul_sq (by positivity : 0 < (4 * b)⁻¹)).norm

theorem product_integrable (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun y : Plane => f (y 0) * g (y 1)) :=
  (volume_preserving_finTwoArrow ℝ).integrable_comp_of_integrable (hf.mul_prod hg)

theorem timeEnvelope_integrable (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Integrable (timeEnvelope a b) :=
  (product_integrable (timeCore b) (timeCore b) (timeCore_integrable hb)
    (timeCore_integrable hb)).const_mul _

private theorem timeDerivativeEnvelope_integrable (a : ℝ) {b : ℝ} (hb : 0 < b)
    (j : Fin 2) : Integrable (timeDerivativeEnvelope a b j) := by
  fin_cases j
  · have h := (product_integrable (fun y => |y| * timeCore b y) (timeCore b)
      (timeMoment_integrable hb) (timeCore_integrable hb)).const_mul
        (timeCoefficient a ^ 2 / (2 * a))
    convert! h using 1
    funext y
    simp only [timeDerivativeEnvelope, timeEnvelope, Fin.reduceFinMk]
    ring
  · have h := (product_integrable (timeCore b) (fun y => |y| * timeCore b y)
      (timeCore_integrable hb) (timeMoment_integrable hb)).const_mul
        (timeCoefficient a ^ 2 / (2 * a))
    convert! h using 1
    funext y
    simp only [timeDerivativeEnvelope, timeEnvelope, Fin.reduceFinMk]
    ring

private theorem oneDim_time_continuousAt {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ContinuousAt (fun s => oneDim s y) t := by
  unfold oneDim
  fun_prop (disch := positivity)

private theorem kernel_time_continuousAt {t : ℝ} (ht : 0 < t) (y : Plane) :
    ContinuousAt (fun s => kernel s y) t :=
  (oneDim_time_continuousAt ht (y 0)).mul (oneDim_time_continuousAt ht (y 1))

private theorem derivative_time_continuousAt {t : ℝ} (ht : 0 < t) (j : Fin 2) (y : Plane) :
    ContinuousAt (fun s => kernelDerivative s j y) t := by
  unfold kernelDerivative
  have hd : ContinuousAt (fun s : ℝ => (2 : ℝ) * s) t :=
    continuousAt_const.mul continuousAt_id
  have hq : ContinuousAt (fun s : ℝ => y j / (2 * s)) t :=
    continuousAt_const.div hd (mul_ne_zero (by norm_num) ht.ne')
  exact hq.neg.mul (kernel_time_continuousAt ht y)

/-- Gaussian kernels are continuous in L1 at every strictly positive time. -/
theorem kernel_l1_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (fun s => ∫ y, |kernel s y - kernel t y|) (𝓝 t) (𝓝 0) := by
  let a := t / 2
  let b := 2 * t
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hat : a < t := by dsimp [a]; linarith
  have htb : t < b := by dsimp [b]; linarith
  have hI : Ioo a b ∈ 𝓝 t := Ioo_mem_nhds hat htb
  have hc : ContinuousAt (fun s => ∫ y, |kernel s y - kernel t y|) t := by
    apply continuousAt_of_dominated (bound := fun y => 2 * timeEnvelope a b y)
    · exact Eventually.of_forall fun s =>
        (((kernel_smooth s).continuous.sub (kernel_smooth t).continuous).abs).aestronglyMeasurable
    · filter_upwards [hI] with s hs
      exact ae_of_all _ fun y => by
        simp only [Real.norm_eq_abs, abs_abs]
        calc
          _ ≤ |kernel s y| + |kernel t y| := abs_sub _ _
          _ = kernel s y + kernel t y := by
            rw [abs_of_nonneg (kernel_nonneg _ _), abs_of_nonneg (kernel_nonneg _ _)]
          _ ≤ timeEnvelope a b y + timeEnvelope a b y :=
            add_le_add (kernel_time_le ha hs.1.le hs.2.le y)
              (kernel_time_le ha hat.le htb.le y)
          _ = _ := by ring
    · exact (timeEnvelope_integrable a hb).const_mul 2
    · exact ae_of_all _ fun y =>
        ((kernel_time_continuousAt ht y).sub continuousAt_const).abs
  simpa only [ContinuousAt, sub_self, abs_zero, integral_zero] using hc

/-- The Cartesian Gaussian derivatives are also continuous in L1 at positive time. -/
theorem kernelDerivative_l1_tendsto {t : ℝ} (ht : 0 < t) (j : Fin 2) :
    Tendsto (fun s => ∫ y, |kernelDerivative s j y - kernelDerivative t j y|) (𝓝 t) (𝓝 0) := by
  let a := t / 2
  let b := 2 * t
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hat : a < t := by dsimp [a]; linarith
  have htb : t < b := by dsimp [b]; linarith
  have hI : Ioo a b ∈ 𝓝 t := Ioo_mem_nhds hat htb
  have hspace (s : ℝ) : Continuous (kernelDerivative s j) := by
    change Continuous (fun y : Plane => -(y j / (2 * s)) * kernel s y)
    convert! ((continuous_apply j).div_const (2 * s)).neg.mul (kernel_smooth s).continuous using 1
  have hc : ContinuousAt (fun s => ∫ y, |kernelDerivative s j y - kernelDerivative t j y|) t := by
    apply continuousAt_of_dominated (bound := fun y => 2 * timeDerivativeEnvelope a b j y)
    · exact Eventually.of_forall fun s => ((hspace s).sub (hspace t)).abs.aestronglyMeasurable
    · filter_upwards [hI] with s hs
      exact ae_of_all _ fun y => by
        simp only [Real.norm_eq_abs, abs_abs]
        calc
          _ ≤ |kernelDerivative s j y| + |kernelDerivative t j y| := abs_sub _ _
          _ ≤ timeDerivativeEnvelope a b j y + timeDerivativeEnvelope a b j y :=
            add_le_add (derivative_time_le ha hs.1.le hs.2.le j y)
              (derivative_time_le ha hat.le htb.le j y)
          _ = _ := by ring
    · exact (timeDerivativeEnvelope_integrable a hb j).const_mul 2
    · exact ae_of_all _ fun y =>
        ((derivative_time_continuousAt ht j y).sub continuousAt_const).abs
  simpa only [ContinuousAt, sub_self, abs_zero, integral_zero] using hc

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Heat operators depend continuously on positive time in the operator norm on C_b^k. -/
theorem continuous_heatOperator (k : ℕ) :
    Continuous (fun t : {t : ℝ // 0 < t} => heatOperator F k t.val t.property) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact BoundedSpatialJets.tendsto_convolutionCLM Plane F (𝓝 t) k volume
    (fun s : {s : ℝ // 0 < s} => kernel s.val) (kernel t.val)
    (fun s => kernel_integrable s.property) (kernel_integrable t.property)
    ((kernel_l1_tendsto t.property).comp continuous_subtype_val.continuousAt)

/-- The singular gradient bound causes no loss of operator continuity away from time zero. -/
theorem continuous_gradientOperator (k : ℕ) (j : Fin 2) :
    Continuous (fun t : {t : ℝ // 0 < t} => gradientOperator F k t.val t.property j) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact BoundedSpatialJets.tendsto_convolutionCLM Plane F (𝓝 t) k volume
    (fun s : {s : ℝ // 0 < s} => kernelDerivative s.val j) (kernelDerivative t.val j)
    (fun s => kernelDerivative_integrable s.property j) (kernelDerivative_integrable t.property j)
    ((kernelDerivative_l1_tendsto t.property j).comp continuous_subtype_val.continuousAt)

end ForcedComputation.PlaneHeat

end

end OAI
