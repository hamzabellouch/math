import OAI.Analysis.LipschitzHilbert.Estimates.ProductSlopePrincipalValue

namespace OAI

/-! A finite sharp truncation is the difference of two actual principal
values; the identity is proved using the continuous symmetric quotient. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert.PacketRepresentation

theorem symmetric_regularized_continuous (F : ℝ → ℂ) (hF : Differentiable ℝ F) :
    Continuous (Function.update (fun t : ℝ => t⁻¹ • (F t-F (-t))) 0
      (deriv (fun t : ℝ => F t-F (-t)) 0)) := by
  let g := fun t : ℝ => F t-F (-t)
  have hg : Differentiable ℝ g := hF.sub (hF.comp differentiable_neg)
  have hg0 : g 0=0 := by simp only [g,neg_zero,sub_self]
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t=0
  · subst t
    apply continuousAt_update_same.mpr
    simpa only [zero_add,hg0,sub_zero] using (hg 0).hasDerivAt.tendsto_slope_zero
  · apply (continuousAt_update_of_ne ht).mpr
    exact (continuousAt_id.inv₀ ht).smul hg.continuous.continuousAt

theorem productSymmetricTruncation_eq_pv_sub (u : (ℝ×ℝ) → ℝ)
    (f : (ℝ×ℝ) → ℂ) (hf : Differentiable ℝ f) (epsilon R : ℝ) (he : 0<epsilon)
    (heR : epsilon≤R) (z : ℝ×ℝ) :
    productSymmetricTruncation u epsilon R f z=
      productSlopePrincipalValue u R f z-productSlopePrincipalValue u epsilon f z := by
  let F := fun t : ℝ => f (productSlopeSample u t z)
  have hF : Differentiable ℝ F := by
    unfold F productSlopeSample
    fun_prop
  let reg := Function.update (fun t : ℝ => t⁻¹ • (F t-F (-t))) 0
    (deriv (fun t : ℝ => F t-F (-t)) 0)
  have hreg : Continuous reg := symmetric_regularized_continuous F hF
  change (∫ t in epsilon..R, t⁻¹ • (F t-F (-t)))=
    (∫ t in (0:ℝ)..R, reg t)-(∫ t in (0:ℝ)..epsilon, reg t)
  rw [←intervalIntegral.integral_add_adjacent_intervals
    (hreg.intervalIntegrable 0 epsilon) (hreg.intervalIntegrable epsilon R),add_sub_cancel_left]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le heR] at ht
  exact (Function.update_of_ne (he.trans_le ht.1).ne'
    (deriv (fun t : ℝ => F t-F (-t)) 0) (fun t : ℝ => t⁻¹ • (F t-F (-t)))).symm

theorem shortSharp_eq_pv_sub (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ)
    (hf : Differentiable ℝ f) (epsilon R : ℝ) (he : 0<epsilon) (heR : epsilon≤R)
    (hR : R≤1/4) :
    shortSlopeOperator (sharpTimeKernel epsilon R) u f=
      productSlopePrincipalValue u R f-productSlopePrincipalValue u epsilon f := by
  funext z
  rw [shortSharp_eq_productSymmetric u f hf.continuous epsilon R he heR hR z,
    productSymmetricTruncation_eq_pv_sub u f hf epsilon R he heR z]
  rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
