import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarTiltedExpectation
import OAI.Probability.SKBarriers.Gaussian.GaussianTiltedCramer

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def ScalarSpinConvex (f : ℝ → ℝ) : Prop :=
  ∀ x, 0 ≤ rootHessian 0 f x ∧ rootHessian 0 f x ≤ 1-(rootGradient 0 f x)^2

theorem ScalarSpinConvex.bounds {f : ℝ → ℝ} (h : ScalarSpinConvex f) (x : ℝ) :
    |rootGradient 0 f x| ≤ 1 ∧ |rootHessian 0 f x| ≤ 1 := by
  have H := h x
  refine ⟨(sq_le_one_iff_abs_le_one _).mp (by linarith),?_⟩
  rw [abs_of_nonneg H.1]
  linarith [sq_nonneg (rootGradient 0 f x)]

def scalarStepLinear (v : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem scalarStepLinear_apply (v : ℝ) (z : ℝ × ℝ) :
    scalarStepLinear v z=z.1+v*z.2 := rfl

@[simp] theorem scalarStep_prefixGradient {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (v : ℝ) (z : ℝ × ℝ) :
    prefixGradient (fun z : ℝ × ℝ => f (z.1+v*z.2)) 1 z=
      rootGradient 0 f (z.1+v*z.2) := by
  have H := ((hf.1.differentiable (by norm_num) (scalarStepLinear v z)).hasFDerivAt.comp z
    (scalarStepLinear v).hasFDerivAt).fderiv
  unfold prefixGradient
  change fderiv ℝ (fun z => f (scalarStepLinear v z)) z (1,0)=_
  simp only [Function.comp_def] at H
  rw [H]
  simp only [ContinuousLinearMap.comp_apply,scalarStepLinear_apply,mul_zero,add_zero]
  rfl

@[simp] theorem scalarStep_prefixHessian {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (v : ℝ) (z : ℝ × ℝ) :
    prefixHessian (fun z : ℝ × ℝ => f (z.1+v*z.2)) 1 1 z=
      rootHessian 0 f (z.1+v*z.2) := by
  have H := hessian_comp_linear f hf.1 (scalarStepLinear v) z (1,0) (1,0)
  simpa only [Hessian,prefixHessian,rootHessian,parameterAxis,scalarStepLinear_apply,mul_zero,add_zero] using H

theorem scalarStep_rootGradient {f : ℝ → ℝ} (hf : BoundedDerivs f) (m v x : ℝ) :
    rootGradient 0 (scalarStep m v f) x=scalarStepAverage m v f (rootGradient 0 f) x := by
  have H := fderiv_gaussianStep_apply (hf.compCLM (scalarStepLinear v)) m x 1
  simpa only [rootGradient,parameterAxis,scalarStep,scalarStepAverage,
    gaussianAverage,scalarStepLinear_apply,scalarStep_prefixGradient hf v,rootGradient,parameterAxis] using H

theorem scalarStep_rootHessian {f : ℝ → ℝ} (hf : BoundedDerivs f) (m v x : ℝ) :
    rootHessian 0 (scalarStep m v f) x=scalarStepAverage m v f (rootHessian 0 f) x+
      m*(scalarStepAverage m v f (fun y => (rootGradient 0 f y)^2) x-
        (scalarStepAverage m v f (rootGradient 0 f) x)^2) := by
  have H := fderiv_fderiv_gaussianStep_apply (hf.compCLM (scalarStepLinear v)) m x 1 1
  simpa only [rootHessian,parameterAxis,scalarStep,scalarStepAverage,
    gaussianAverage,scalarStepLinear_apply,scalarStep_prefixGradient hf v,scalarStep_prefixHessian hf v,rootHessian,parameterAxis,pow_two] using H

theorem scalarStepAverage_continuous {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |g x| ≤ B) (m v : ℝ) :
    Continuous (scalarStepAverage m v f g) := by
  apply gaussianAverage_continuous (hf.compCLM (scalarStepLinear v)) m
    (hg.comp (scalarStepLinear v).continuous) hB
  intro z
  exact hb _

theorem scalarStepAverage_bound {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    {B : ℝ} (hb : ∀ x, |g x| ≤ B) (m v x : ℝ) :
    |scalarStepAverage m v f g x| ≤ B := by
  exact gaussianAverage_norm_le (hf.compCLM (scalarStepLinear v)) m
    (g:=fun z => g (z.1+v*z.2)) (fun z => hb _) x

theorem scalarStepAverage_integrable {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) {B : ℝ} (hb : ∀ x, |g x| ≤ B) (m v x : ℝ) :
    Integrable (fun y => g (x+v*y)) (gaussianStepLaw m (fun z : ℝ×ℝ => f (z.1+v*z.2)) x) := by
  exact integrable_gaussianStep_of_bounded (hf.compCLM (scalarStepLinear v)) m x
    (hg.comp (continuous_const.add (continuous_const.mul continuous_id))) (fun y => hb _)

theorem scalarStepAverage_variance_nonneg {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) {B : ℝ} (hb : ∀ x, |g x| ≤ B) (m v x : ℝ) :
    0 ≤ scalarStepAverage m v f (fun y => (g y)^2) x-(scalarStepAverage m v f g x)^2 := by
  have : IsProbabilityMeasure (gaussianStepLaw m (fun z : ℝ×ℝ => f (z.1+v*z.2)) x) :=
    gaussianStepLaw_probability (hf.compCLM (scalarStepLinear v)) m x
  have H : MemLp (fun y => g (x+v*y)) 2
      (gaussianStepLaw m (fun z : ℝ×ℝ => f (z.1+v*z.2)) x) :=
    MemLp.of_bound (hg.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
      B (ae_of_all _ (fun y => hb _))
  simpa only [scalarStepAverage,gaussianAverage,variance_eq_sub H,Pi.pow_apply] using variance_nonneg (X:=fun y => g (x+v*y))
    (μ:=gaussianStepLaw m (fun z : ℝ×ℝ => f (z.1+v*z.2)) x)

theorem ScalarSpinConvex.scalarStep {f : ℝ → ℝ} (h : ScalarSpinConvex f)
    (hf : BoundedDerivs f) {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v : ℝ) :
    ScalarSpinConvex (scalarStep m v f) := by
  intro x
  have : IsProbabilityMeasure (gaussianStepLaw m (fun z : ℝ×ℝ => f (z.1+v*z.2)) x) :=
    gaussianStepLaw_probability (hf.compCLM (scalarStepLinear v)) m x
  have hχ := rootHessian_continuous 0 hf
  have hu := rootGradient_continuous 0 hf
  have hiχ := scalarStepAverage_integrable hf hχ (fun y => (h.bounds y).2) m v x
  have hiu2 := scalarStepAverage_integrable hf (hu.pow 2)
    (fun y => show |(rootGradient 0 f y)^2| ≤ 1 from by
      rw [abs_of_nonneg (sq_nonneg _)]; exact (sq_le_one_iff_abs_le_one _).mpr (h.bounds y).1) m v x
  have HP : 0 ≤ scalarStepAverage m v f (rootHessian 0 f) x := integral_nonneg (fun y => (h _).1)
  have HV := scalarStepAverage_variance_nonneg hf hu (fun y => (h.bounds y).1) m v x
  have HU : scalarStepAverage m v f (rootHessian 0 f) x+
      scalarStepAverage m v f (fun y => (rootGradient 0 f y)^2) x ≤ 1 := by
    have H := integral_mono (hiχ.add hiu2) (integrable_const (1:ℝ))
      (fun y => show rootHessian 0 f (x+v*y)+(rootGradient 0 f (x+v*y))^2 ≤ 1 by linarith [(h (x+v*y)).2])
    simp only [Pi.add_apply] at H
    rw [integral_add hiχ hiu2,integral_const,probReal_univ,one_smul] at H
    exact H
  rw [scalarStep_rootHessian hf,scalarStep_rootGradient hf]
  constructor
  · exact add_nonneg HP (mul_nonneg hm.1 HV)
  · nlinarith [mul_nonneg (sub_nonneg.mpr hm.2) HV]

theorem scalarStepAverage_cramer {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (h : ScalarSpinConvex f) {m : ℝ} (hm : 0 ≤ m) (v x : ℝ) :
    v^2*(scalarStepAverage m v f (rootHessian 0 f) x)^2 ≤
      scalarStepAverage m v f (fun y => (rootGradient 0 f y)^2) x-
        (scalarStepAverage m v f (rootGradient 0 f) x)^2 := by
  have hdf (y : ℝ) : HasDerivAt f (rootGradient 0 f y) y :=
    (hf.1.differentiable (by norm_num) y).hasDerivAt
  have hdu (y : ℝ) : HasDerivAt (rootGradient 0 f) (rootHessian 0 f y) y := by
    simpa only [parameterAxis,smul_eq_mul,mul_one,zero_add] using rootGradientLine_hasDerivAt 0 hf 0 y
  have hcχ : Continuous (fun y : ℝ => rootHessian 0 f (x+v*y)) :=
    (rootHessian_continuous 0 hf).comp (continuous_const.add (continuous_const.mul continuous_id))
  have hV (y : ℝ) : HasDerivAt (fun y => m*f (x+v*y)) (m*v*rootGradient 0 f (x+v*y)) y := by
    convert ((hdf (x+v*y)).comp y (((hasDerivAt_id y).const_mul v).const_add x)).const_mul m using 1
    all_goals first | rfl | exact Subsingleton.elim _ _ | ring
  have hV' (y : ℝ) : HasDerivAt (fun y => m*v*rootGradient 0 f (x+v*y))
      (m*v^2*rootHessian 0 f (x+v*y)) y := by
    convert ((hdu (x+v*y)).comp y (((hasDerivAt_id y).const_mul v).const_add x)).const_mul (m*v) using 1
    all_goals first | rfl | exact Subsingleton.elim _ _ | ring
  have hg (y : ℝ) : HasDerivAt (fun y => rootGradient 0 f (x+v*y))
      (v*rootHessian 0 f (x+v*y)) y := by
    convert (hdu (x+v*y)).comp y (((hasDerivAt_id y).const_mul v).const_add x) using 1
    all_goals first | rfl | exact Subsingleton.elim _ _ | ring
  have hbu : HasExpGrowth (fun y => rootGradient 0 f (x+v*y)) :=
    HasExpGrowth.of_bounded zero_le_one (fun y => (h.bounds _).1)
  have hbχ : HasExpGrowth (fun y => rootHessian 0 f (x+v*y)) :=
    HasExpGrowth.of_bounded zero_le_one (fun y => (h.bounds _).2)
  have hconst (c : ℝ) : HasExpGrowth (fun _ : ℝ => c) :=
    HasExpGrowth.of_bounded (norm_nonneg c) (fun _ => le_rfl)
  have hreg : BoundedDerivs (fun y => f (x+v*y)) :=
    (hf.translate x).compCLM (v • ContinuousLinearMap.id ℝ ℝ)
  have H := gaussian_tilted_cramer hV hV' hg (hreg.exp_growths m).1
    ((hconst (m*v)).mul hbu) ((hconst (m*v^2)).mul hbχ) hbu ((hconst v).mul hbχ)
    (continuous_const.mul hcχ) (continuous_const.mul hcχ)
    (fun y => mul_nonneg (mul_nonneg hm (sq_nonneg v)) (h _).1)
  rw [integral_const_mul,mul_pow] at H
  exact H

end SK.Analytic

end
end

end OAI
