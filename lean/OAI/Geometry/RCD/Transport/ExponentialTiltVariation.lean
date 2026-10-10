import OAI.Geometry.RCD.Coordinates.NormalizedExponentialTilt
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! # Exact first variations of compact exponential density perturbations -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

 theorem exponential_tilt_integral_hasDerivAt_zero {r g : X → ℝ}
    (hr : Integrable r μ) (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) :
    HasDerivAt (fun t : ℝ => ∫ x, Real.exp (t*g x)*r x ∂μ)
      (∫ x, g x*r x ∂μ) 0 := by
  let F := fun (t : ℝ) x => Real.exp (t*g x)*r x
  let F' := fun (t : ℝ) x => Real.exp (t*g x)*g x*r x
  have hF (t : ℝ) : AEStronglyMeasurable (F t) μ :=
    ((Real.measurable_exp.comp (measurable_const.mul hg)).aestronglyMeasurable).mul hr.aestronglyMeasurable
  have hD : AEStronglyMeasurable (F' 0) μ := by
    convert hg.aestronglyMeasurable.mul hr.aestronglyMeasurable using 1
    ext x
    simp only [F',zero_mul,Real.exp_zero,one_mul,Pi.mul_apply]
  have hbound : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (-1:ℝ) 1,
      ‖F' t x‖ ≤ (Real.exp M*M)*‖r x‖ := .of_forall fun x t ht => by
    have ht1 : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le,ht.2.le⟩
    have htg : t*g x ≤ (M:ℝ) := by
      calc
        _ ≤ |t*g x| := le_abs_self _
        _ = |t| *|g x| := abs_mul _ _
        _ ≤ 1*M := mul_le_mul ht1 (hgb x) (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    dsimp only [F']
    rw [norm_mul,norm_mul,Real.norm_eq_abs (Real.exp _),abs_of_pos (Real.exp_pos _),Real.norm_eq_abs (g x)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (Real.exp_le_exp.mpr htg) (hgb x) (abs_nonneg _) (Real.exp_pos _).le) (norm_nonneg _)
  have hderiv : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (-1:ℝ) 1, HasDerivAt (fun s => F s x) (F' t x) t :=
    .of_forall fun x t _ => by
      simpa only [F,F',id_eq,one_mul] using
        (((hasDerivAt_id t).mul_const (g x)).exp).mul_const (r x)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0) zero_lt_one) (.of_forall hF)
    (show Integrable (F 0) μ by simpa only [F,zero_mul,Real.exp_zero,one_mul] using hr)
    hD hbound (hr.norm.const_mul (Real.exp M*M)) hderiv).2
  simpa only [F,F',zero_mul,Real.exp_zero,one_mul] using h

 theorem normalized_tilt_hasDerivAt_zero {r g : X → ℝ}
    (hr : Integrable r μ) (hm : (∫ x, r x ∂μ)=1) (hg : Measurable g)
    {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (x : X) :
    HasDerivAt (fun t : ℝ => (∫ y, Real.exp (t*g y)*r y ∂μ)⁻¹*(Real.exp (t*g x)*r x))
      (r x*(g x-(∫ y, g y*r y ∂μ))) 0 := by
  have h0 : (∫ y, Real.exp ((0:ℝ)*g y)*r y ∂μ)=1 := by
    simpa only [zero_mul,Real.exp_zero,one_mul] using hm
  have hD := (exponential_tilt_integral_hasDerivAt_zero μ hr hg hgb).inv (by rw [h0]; norm_num)
  have hE : HasDerivAt (fun t : ℝ => Real.exp (t*g x)*r x) (g x*r x) 0 := by
    simpa only [id_eq,zero_mul,Real.exp_zero,one_mul] using
      (((hasDerivAt_id (0:ℝ)).mul_const (g x)).exp).mul_const (r x)
  convert hD.mul hE using 1
  simp only [Pi.inv_apply,zero_mul,Real.exp_zero,one_mul,hm,one_pow,div_one,inv_one]
  ring

end RegularPointCoordinates

end

end OAI
