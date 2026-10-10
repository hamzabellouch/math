import OAI.Analysis.LipschitzHilbert.Estimates.ProductSlopePrincipalValue
import OAI.Analysis.LipschitzHilbert.Fourier.SchwartzGlobalLipschitz

namespace OAI

/-! Pointwise domination of short principal values on globally Lipschitz
inputs. No operator estimate or published input is used. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace LipschitzHilbert.PacketRepresentation

theorem productSlopeSample_symmetric_dist (u : (ℝ×ℝ) → ℝ) (z : ℝ×ℝ)
    (hu : |u z|≤1) (t : ℝ) :
    dist (productSlopeSample u t z) (productSlopeSample u (-t) z)≤2*|t| := by
  rw [Prod.dist_eq]
  apply max_le
  · change |(z.1-t)-(z.1- -t)|≤2*|t|
    have he : (z.1-t)-(z.1- -t)= -2*t := by ring
    rw [he,abs_mul]
    norm_num
  · change |(z.2-t*u z)-(z.2- -t*u z)|≤2*|t|
    have he : (z.2-t*u z)-(z.2- -t*u z)=(-2*t)*u z := by ring
    rw [he,abs_mul,abs_mul]
    norm_num only [abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith [abs_nonneg t]

theorem productSymmetricIntegrand_bound (u : (ℝ×ℝ) → ℝ) (z : ℝ×ℝ)
    (hu : |u z|≤1) (f : (ℝ×ℝ) → ℂ) {K : ℝ≥0} (hf : LipschitzWith K f) (t : ℝ) :
    ‖t⁻¹ • (f (productSlopeSample u t z)-f (productSlopeSample u (-t) z))‖≤2*(K:ℝ) := by
  have h := (hf.dist_le_mul (productSlopeSample u t z) (productSlopeSample u (-t) z)).trans
    (mul_le_mul_of_nonneg_left (productSlopeSample_symmetric_dist u z hu t) K.coe_nonneg)
  rw [dist_eq_norm] at h
  rw [norm_smul,Real.norm_eq_abs,abs_inv]
  by_cases ht : t=0
  · simp [ht]
  · have htpos := abs_pos.mpr ht
    calc
      _ ≤ |t|⁻¹*((K:ℝ)*(2*|t|)) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr htpos.le)
      _ = 2*(K:ℝ) := by field_simp

theorem productSymmetricTruncation_pointwise_bound (u : (ℝ×ℝ) → ℝ) (z : ℝ×ℝ)
    (hu : |u z|≤1) (f : (ℝ×ℝ) → ℂ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (epsilon R : ℝ) (he : 0≤epsilon) (heR : epsilon≤R) :
    ‖productSymmetricTruncation u epsilon R f z‖≤2*(K:ℝ)*R := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t (_ : t∈Set.uIoc epsilon R) => productSymmetricIntegrand_bound u z hu f hf t)
  rw [abs_of_nonneg (sub_nonneg.mpr heR)] at h
  exact h.trans (by nlinarith [K.coe_nonneg])

theorem productSlopePrincipalValue_pointwise_bound (u : (ℝ×ℝ) → ℝ) (z : ℝ×ℝ)
    (hu : |u z|≤1) (f : (ℝ×ℝ) → ℂ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (hfd : Differentiable ℝ f) (R : ℝ) (hR : 0<R) :
    ‖productSlopePrincipalValue u R f z‖≤2*(K:ℝ)*R := by
  apply le_of_tendsto (productSymmetricTruncation_tendsto u f hfd R hR z).norm
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds]
    with epsilon he heR
  exact productSymmetricTruncation_pointwise_bound u z hu f hf epsilon R he.le heR.le

theorem productSchwartzPV_pointwise_bound (u : (ℝ×ℝ) → ℝ) (z : ℝ×ℝ)
    (hu : |u z|≤1) (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ) (hR : 0<R) :
    ‖productSlopePrincipalValue u R f z‖≤2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ)*R :=
  productSlopePrincipalValue_pointwise_bound u z hu f (_root_.OAI.SchwartzMap.global_lipschitz f) f.differentiable R hR

end LipschitzHilbert.PacketRepresentation

end

end OAI
