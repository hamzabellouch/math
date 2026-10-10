import Mathlib
import OAI.Geometry.IntegralFillings.Charts.ChangeVariables

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
noncomputable def differentialOrientation (d : ℝ) : ℤ := if 0 ≤ d then 1 else -1

lemma abs_mul_differentialOrientation (d : ℝ) :
    |d| * (differentialOrientation d : ℝ) = d := by
  by_cases hd : 0 ≤ d
  · simp [differentialOrientation,hd,abs_of_nonneg hd]
  · simp [differentialOrientation,hd,abs_of_neg (lt_of_not_ge hd)]

lemma signed_lipschitzOn_changeVariables {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (hinj : InjOn f s)
    (θ : E → ℤ) (g : E → ℝ) :
    ∫ y in f '' s, ((θ (Function.invFunOn f s y) *
      differentialOrientation (fderivWithin ℝ f s (Function.invFunOn f s y)).det : ℤ) : ℝ) * g y ∂μ =
    ∫ x in s, (θ x : ℝ) * (fderivWithin ℝ f s x).det * g (f x) ∂μ := by
  rw [integral_image_eq_integral_abs_det_within μ hs hf hinj]
  apply setIntegral_congr_fun hs
  intro x hx
  dsimp only
  rw [hinj.leftInvOn_invFunOn hx,Int.cast_mul,smul_eq_mul]
  have heq := abs_mul_differentialOrientation (fderivWithin ℝ f s x).det
  calc
    _ = (θ x : ℝ) * (|(fderivWithin ℝ f s x).det| *
      (differentialOrientation (fderivWithin ℝ f s x).det : ℝ)) * g (f x) := by ring
    _ = _ := by rw [heq]

lemma integrableOn_oriented_multiplicity_image {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (hinj : InjOn f s)
    {θ : E → ℤ} (hθ : IntegrableOn (fun x => (θ x : ℝ)) s μ) :
    IntegrableOn (fun y => ((θ (Function.invFunOn f s y) *
      differentialOrientation (fderivWithin ℝ f s (Function.invFunOn f s y)).det : ℤ) : ℝ))
      (f '' s) μ := by
  rw [integrableOn_image_iff_integrableOn_abs_det_within μ hs hf hinj]
  apply (integrable_mul_det_fderivWithin_lipschitzOn μ hs hf hθ).congr
  filter_upwards [ae_restrict_mem hs] with x hx
  rw [hinj.leftInvOn_invFunOn hx,Int.cast_mul,smul_eq_mul]
  rw [←mul_assoc,mul_comm _ (θ x : ℝ),mul_assoc,abs_mul_differentialOrientation]

lemma ae_det_fderivWithin_comp_bilipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K L : ℝ≥0} (hf : LipschitzOnWith K f s)
    (ha : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ (L : ℝ) * dist (f x) (f y))
    {g : E → E} {J : ℝ≥0} (hg : LipschitzOnWith J g (f '' s)) :
    ∀ᵐ x ∂μ.restrict s, (fderivWithin ℝ (g ∘ f) s x).det =
      (fderivWithin ℝ g (f '' s) (f x)).det * (fderivWithin ℝ f s x).det := by
  filter_upwards [ae_fderivWithin_comp_bilipschitzOn μ hs hf ha hg] with x hx
  rw [hx]
  exact LinearMap.det_comp _ _

end SharpIntegralFillings

end

end OAI
