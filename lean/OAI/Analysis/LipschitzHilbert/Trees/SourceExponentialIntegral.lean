import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! Integration of the scalar exponential terms appearing in a source
packet amplitude. On each exhaustion set the logarithmic coefficients
are bounded, so the integrated affine slice is entire. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace LipschitzHilbert
variable {X : Type*} [MeasurableSpace X]

theorem source_affine_exp_norm_le {c d z : ℂ} {B R : ℝ}
    (_hB : 0 ≤ B) (hR : 0 ≤ R) (hc : ‖c‖ ≤ B) (hd : ‖d‖ ≤ B) (hz : ‖z‖ ≤ R) :
    ‖Complex.exp (c+z*d)‖ ≤ Real.exp (B+R*B) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ‖c+z*d‖ := Complex.re_le_norm _
    _ ≤ ‖c‖+‖z*d‖ := norm_add_le _ _
    _ = ‖c‖+‖z‖*‖d‖ := by rw [norm_mul]
    _ ≤ B+R*B := add_le_add hc (mul_le_mul hz hd (norm_nonneg _) hR)

theorem source_integral_affine_exp_entire (μ : Measure X)
    (a c d : X → ℂ) (ha : Measurable a) (hc : Measurable c) (hd : Measurable d)
    (haint : Integrable a μ) (B : ℝ) (hB : 0 ≤ B)
    (hcB : ∀ x, ‖c x‖ ≤ B) (hdB : ∀ x, ‖d x‖ ≤ B) :
    Differentiable ℂ (fun z => ∫ x, a x*Complex.exp (c x+z*d x) ∂μ) := by
  intro z0
  have hmeas (z : ℂ) : Measurable (fun x => a x*Complex.exp (c x+z*d x)) :=
    ha.mul (Complex.continuous_exp.measurable.comp (hc.add (hd.const_mul z)))
  have hpoint (z : ℂ) (x : X) :
      ‖a x*Complex.exp (c x+z*d x)‖ ≤ ‖a x‖*Real.exp (B+‖z‖*B) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (source_affine_exp_norm_le hB (norm_nonneg z) (hcB x) (hdB x) le_rfl) (norm_nonneg _)
  have hint (z : ℂ) : Integrable (fun x => a x*Complex.exp (c x+z*d x)) μ :=
    (haint.norm.mul_const (Real.exp (B+‖z‖*B))).mono' (hmeas z).aestronglyMeasurable
      (Eventually.of_forall (hpoint z))
  let derivative := fun z x => a x*(Complex.exp (c x+z*d x)*d x)
  have hderiv (z : ℂ) (x : X) : HasDerivAt
      (fun z => a x*Complex.exp (c x+z*d x)) (derivative z x) z := by
    simpa only [one_mul,derivative,id_eq] using
      ((((hasDerivAt_id z).mul_const (d x)).const_add (c x)).cexp).const_mul (a x)
  have hDmeas : AEStronglyMeasurable (derivative z0) μ :=
    (ha.mul ((Complex.continuous_exp.measurable.comp (hc.add (hd.const_mul z0))).mul hd)).aestronglyMeasurable
  have hDbound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball z0 1,
      ‖derivative z x‖ ≤ ‖a x‖*(Real.exp (B+(‖z0‖+1)*B)*B) := by
    apply Eventually.of_forall
    intro x z hz
    have hzR : ‖z‖ ≤ ‖z0‖+1 := (norm_lt_of_mem_ball hz).le
    have he := source_affine_exp_norm_le hB (by positivity : 0 ≤ ‖z0‖+1)
      (hcB x) (hdB x) hzR
    dsimp only [derivative]
    rw [norm_mul,norm_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul he (hdB x) (norm_nonneg _) (Real.exp_pos _).le) (norm_nonneg _)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z0 (by norm_num : (0:ℝ) < 1))
    (Eventually.of_forall fun z => (hmeas z).aestronglyMeasurable) (hint z0) hDmeas hDbound
    (haint.norm.mul_const (Real.exp (B+(‖z0‖+1)*B)*B))
    (Eventually.of_forall fun x z _ => hderiv z x)
  exact h.2.differentiableAt

end LipschitzHilbert

end

end OAI
