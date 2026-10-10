import OAI.Probability.GammaPassage.Environment
import OAI.Probability.GammaPassage.MGF
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ν : Measure ℝ} {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}

/-- The cost of a deterministic finite set of distinct undirected edges. -/
def edgeSum (S : Finset PlanarFPP.Edge) (τ : PlanarFPP.Edge → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ e ∈ S, τ e ω

omit [MeasurableSpace Ω] in
@[simp] lemma edgeSum_empty (τ : PlanarFPP.Edge → Ω → ℝ) (ω : Ω) :
    edgeSum ∅ τ ω = 0 := by simp [edgeSum]

lemma IidEnvironment.measurable_edgeSum (h : IidEnvironment ν P τ)
    (S : Finset PlanarFPP.Edge) : Measurable (edgeSum S τ) :=
  Finset.measurable_sum S (fun e _ => h.measurable e)

/-- Integral transport along the joint law of a finite edge set. -/
lemma IidEnvironment.integral_finiteJoint (h : IidEnvironment ν P τ)
    (S : Finset PlanarFPP.Edge) (f : (S → ℝ) → ℝ) (hf : Measurable f) :
    (∫ ω, f (fun e : S => τ e ω) ∂P) =
      ∫ x : S → ℝ, f x ∂Measure.pi (fun _ : S => ν) := by
  rw [← h.finiteJointLaw S]
  exact (integral_map
    (Measurable.of_eval (fun e : S => h.measurable e)).aemeasurable
    hf.aestronglyMeasurable).symm

variable {shape rate theta : ℝ}

/-- The exponential moment of a finite edge sum, obtained by finite-product integration. -/
theorem GammaEnvironment.integral_exp_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta : theta < rate) (S : Finset PlanarFPP.Edge) :
    (∫ ω, Real.exp (theta * edgeSum S τ ω) ∂P) =
      ((rate / (rate - theta)) ^ shape) ^ S.card := by
  classical
  let : IsProbabilityMeasure (gammaMeasure shape rate) :=
    isProbabilityMeasure_gammaMeasure hshape hrate
  have hpoint (ω : Ω) : Real.exp (theta * edgeSum S τ ω) =
      ∏ e : S, Real.exp (theta * τ e ω) := by
    rw [edgeSum, ← Finset.sum_coe_sort, Finset.mul_sum, Real.exp_sum]
  simp_rw [hpoint]
  rw [h.integral_finiteJoint S (fun x : S → ℝ => ∏ e : S, Real.exp (theta * x e))
    (by fun_prop)]
  rw [integral_fintype_prod_eq_prod (ι := S) (E := fun _ : S => ℝ)
    (μ := fun _ : S => gammaMeasure shape rate)
    (fun (_ : S) (x : ℝ) => Real.exp (theta * x))]
  simp only [gamma_integral_exp hshape hrate htheta, Finset.prod_const,
    Finset.card_univ, Fintype.card_coe]

/-- The nonnegative exponential moment of a finite iid Gamma edge sum. -/
theorem GammaEnvironment.lintegral_exp_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta : theta < rate) (S : Finset PlanarFPP.Edge) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) ∂P) =
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card := by
  classical
  let X : PlanarFPP.Edge → Ω → ℝ≥0∞ :=
    fun e ω => ENNReal.ofReal (Real.exp (theta * τ e ω))
  have hX : ∀ e, Measurable (X e) := by
    intro e
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (h.measurable e)))
  have hXi : iIndepFun X P := h.independent.comp
    (fun _ (x : ℝ) => ENNReal.ofReal (Real.exp (theta * x))) (fun _ => by fun_prop)
  have hpoint (ω : Ω) : ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) =
      ∏ e ∈ S, X e ω := by
    rw [edgeSum, Finset.mul_sum, Real.exp_sum]
    exact ENNReal.ofReal_prod_of_nonneg (fun e _ => (Real.exp_pos _).le)
  have hm (e : PlanarFPP.Edge) :
      (∫⁻ ω, X e ω ∂P) = ENNReal.ofReal ((rate / (rate - theta)) ^ shape) := by
    change (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * τ e ω)) ∂P) = _
    rw [← lintegral_map (f := fun x : ℝ => ENNReal.ofReal (Real.exp (theta * x)))
      (by fun_prop) (h.measurable e), h.marginal e]
    exact gamma_lintegral_exp hshape hrate htheta
  simp_rw [hpoint]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun S X hXi hX]
  simp only [hm, Finset.prod_const]

/-- Exponential functions of finite edge sums are integrable for `theta < rate`. -/
theorem GammaEnvironment.integrable_exp_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta : theta < rate) (S : Finset PlanarFPP.Edge) :
    Integrable (fun ω => Real.exp (theta * edgeSum S τ ω)) P := by
  have hm : Measurable (fun ω => Real.exp (theta * edgeSum S τ ω)) :=
    Real.measurable_exp.comp (measurable_const.mul (h.measurable_edgeSum S))
  apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)).mp
  rw [h.lintegral_exp_edgeSum hshape hrate htheta S]
  exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

end GammaFPP

end OAI
