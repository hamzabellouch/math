import OAI.Analysis.LipschitzHilbert.Estimates.ProductSlopePrincipalValue
import Mathlib.MeasureTheory.Function.LpSpace.Complete

namespace OAI

/-! Fatou passage from uniform actual sharp truncations to the pointwise
symmetric principal value in product coordinates. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace LipschitzHilbert.PacketRepresentation

def pvInnerRadius (R : ℝ) (n : ℕ) : ℝ := R/((n:ℝ)+2)

theorem pvInnerRadius_pos (R : ℝ) (hR : 0<R) (n : ℕ) : 0<pvInnerRadius R n := by
  unfold pvInnerRadius
  positivity

theorem pvInnerRadius_lt (R : ℝ) (hR : 0<R) (n : ℕ) : pvInnerRadius R n<R := by
  unfold pvInnerRadius
  apply (div_lt_iff₀ (by positivity : 0<(n:ℝ)+2)).mpr
  nlinarith only [Nat.cast_nonneg (α:=ℝ) n,hR]

theorem pvInnerRadius_tendsto (R : ℝ) (hR : 0<R) :
    Tendsto (pvInnerRadius R) atTop (𝓝[>] (0:ℝ)) := by
  have hs := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ) |>.comp (tendsto_add_atTop_nat 1)
  have heq : pvInnerRadius R=(fun n : ℕ => R*((((n+1:ℕ):ℝ)+1)⁻¹)) := by
    funext n
    norm_num [pvInnerRadius,div_eq_mul_inv,Nat.cast_add,add_assoc]
  have hzero : Tendsto (pvInnerRadius R) atTop (𝓝 (0:ℝ)) := by
    rw [heq]
    simpa only [Function.comp_def,one_div,mul_zero] using (tendsto_const_nhds (x:=R)).mul hs
  exact tendsto_nhdsWithin_iff.mpr ⟨hzero,Eventually.of_forall (pvInnerRadius_pos R hR)⟩

theorem shortSharp_tendsto_productSlopePrincipalValue (u : (ℝ×ℝ) → ℝ)
    (f : (ℝ×ℝ) → ℂ) (hf : Differentiable ℝ f) (R : ℝ) (hR : 0<R) (hRsmall : R≤1/4)
    (z : ℝ×ℝ) :
    Tendsto (fun n => shortSlopeOperator (sharpTimeKernel (pvInnerRadius R n) R) u f z)
      atTop (𝓝 (productSlopePrincipalValue u R f z)) := by
  have h := (productSymmetricTruncation_tendsto u f hf R hR z).comp (pvInnerRadius_tendsto R hR)
  apply h.congr'
  filter_upwards [] with n
  exact (shortSharp_eq_productSymmetric u f hf.continuous _ R (pvInnerRadius_pos R hR n)
    (pvInnerRadius_lt R hR n).le hRsmall z).symm

theorem productSlopePrincipalValue_measurable (u : (ℝ×ℝ) → ℝ) (hu : Measurable u)
    (f : (ℝ×ℝ) → ℂ) (hf : Differentiable ℝ f) (R : ℝ) (hR : 0<R) (hRsmall : R≤1/4) :
    Measurable (productSlopePrincipalValue u R f) := by
  apply measurable_of_tendsto_metrizable
    (fun n => shortSlopeOperator_measurable _ (sharpTimeKernel_measurable _ R) u hu f hf.continuous.measurable)
  exact tendsto_pi_nhds.mpr (shortSharp_tendsto_productSlopePrincipalValue u f hf R hR hRsmall)

theorem productSlopePrincipalValue_eLpNorm_le (u : (ℝ×ℝ) → ℝ) (hu : Measurable u)
    (f : (ℝ×ℝ) → ℂ) (hf : Differentiable ℝ f) (R : ℝ) (hR : 0<R) (hRsmall : R≤1/4)
    (C : ℝ≥0∞)
    (hbound : ∀ epsilon : ℝ, 0<epsilon → epsilon<R →
      eLpNorm (shortSlopeOperator (sharpTimeKernel epsilon R) u f) 2 planeMeasure≤C) :
    eLpNorm (productSlopePrincipalValue u R f) 2 planeMeasure≤C := by
  apply Lp.eLpNorm_le_of_ae_tendsto (u:=(atTop : Filter ℕ))
    (Eventually.of_forall fun n => hbound _ (pvInnerRadius_pos R hR n) (pvInnerRadius_lt R hR n))
    (fun n => (shortSlopeOperator_measurable _ (sharpTimeKernel_measurable _ R) u hu f hf.continuous.measurable).aestronglyMeasurable)
    (productSlopePrincipalValue_measurable u hu f hf R hR hRsmall).aestronglyMeasurable
  exact Eventually.of_forall (shortSharp_tendsto_productSlopePrincipalValue u f hf R hR hRsmall)

end LipschitzHilbert.PacketRepresentation

end

end OAI
