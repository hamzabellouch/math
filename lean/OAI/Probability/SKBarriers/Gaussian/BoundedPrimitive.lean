import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarTiltedExpectation

namespace OAI

section

noncomputable section
open scoped Topology NNReal ContDiff
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem boundedDerivs_of_derivatives {f g dg : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt f (g x) x) (hdg : ∀ x, HasDerivAt g (dg x) x)
    (hcont : Continuous dg) {B C : ℝ≥0}
    (hB : ∀ x, |g x| ≤ B) (hC : ∀ x, |dg x| ≤ C) : BoundedDerivs f := by
  have he : deriv f=g := funext (fun x => (hg x).deriv)
  have he' : deriv g=dg := funext (fun x => (hdg x).deriv)
  have hgc : ContDiff ℝ 1 g := contDiff_one_iff_deriv.mpr
    ⟨fun x => (hdg x).differentiableAt,he' ▸ hcont⟩
  have hfc : ContDiff ℝ 2 f := by
    rw [show (2:ℕ∞ω)=1+1 by norm_num,contDiff_succ_iff_deriv]
    exact ⟨fun x => (hg x).differentiableAt,by norm_num,he ▸ hgc⟩
  have hfe : fderiv ℝ f=fun x => g x • (ContinuousLinearMap.id ℝ ℝ) := by
    funext x
    apply ContinuousLinearMap.ext
    intro y
    simp only [smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul,
      fderiv_eq_deriv_mul,he]
  refine ⟨hfc,B,C,B.coe_nonneg,C.coe_nonneg,?_,?_⟩
  · intro x
    rw [← norm_deriv_eq_norm_fderiv,he,Real.norm_eq_abs]
    exact hB x
  · intro x
    rw [hfe,← norm_deriv_eq_norm_fderiv,((hdg x).smul_const (ContinuousLinearMap.id ℝ ℝ)).deriv,
      norm_smul,ContinuousLinearMap.norm_id,Real.norm_eq_abs,mul_one]
    exact hC x

def boundedPrimitive (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in 0..x, g y

theorem boundedPrimitive_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    HasDerivAt (boundedPrimitive g) (g x) x :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 x)
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

theorem boundedPrimitive_regular {g dg : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (dg x) x) (hdg : Continuous dg)
    {B C : ℝ≥0} (hB : ∀ x, |g x| ≤ B) (hC : ∀ x, |dg x| ≤ C) :
    BoundedDerivs (boundedPrimitive g) :=
  boundedDerivs_of_derivatives
    (boundedPrimitive_hasDerivAt (continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt))) hg hdg hB hC

theorem boundedPrimitive_lipschitz {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ≥0}
    (hB : ∀ x, |g x| ≤ B) : LipschitzWith B (boundedPrimitive g) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (boundedPrimitive_hasDerivAt hg x).differentiableAt)
  intro x
  rw [(boundedPrimitive_hasDerivAt hg x).deriv]
  exact_mod_cast hB x

theorem dyadicScalarAverage_tendsto_C1 (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g dg : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : ∀ y, HasDerivAt g (dg y) y) (hdg : Continuous dg)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f)
    (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    Tendsto (fun n => dyadicScalarAverage β α n s t f g x) atTop
      (𝓝 (scalarCDFAverage β α s t f g x)) := by
  have hc : Continuous g := continuous_iff_continuousAt.mpr (fun y => (hg y).continuousAt)
  exact dyadicScalarAverage_tendsto β hα hmono hf (boundedPrimitive_regular hg hdg hB hC)
    (boundedPrimitive_hasDerivAt hc) hg hfK (boundedPrimitive_lipschitz hc hB) hB hC s t ht x

end SK.Analytic

end
end

end OAI
