import OAI.Analysis.LipschitzHilbert.Fourier.SharpKernelSymmetrization
import OAI.Analysis.LipschitzHilbert.Estimates.ShortSlopeCommutation
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! Pointwise principal values for smooth functions in the product-plane
coordinates used by the actual band operators. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

def productSlopeSample (u : (ℝ×ℝ) → ℝ) (t : ℝ) (z : ℝ×ℝ) : ℝ×ℝ :=
  (z.1-t,z.2-t*u z)

def productSymmetricTruncation (u : (ℝ×ℝ) → ℝ) (epsilon R : ℝ)
    (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) : ℂ :=
  ∫ t in epsilon..R, t⁻¹ • (f (productSlopeSample u t z)-f (productSlopeSample u (-t) z))

def productSlopePrincipalValue (u : (ℝ×ℝ) → ℝ) (R : ℝ)
    (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) : ℂ :=
  let g := fun t : ℝ => f (productSlopeSample u t z)-f (productSlopeSample u (-t) z)
  ∫ t in (0:ℝ)..R, Function.update (fun t => t⁻¹ • g t) 0 (deriv g 0) t

theorem productSymmetricTruncation_tendsto (u : (ℝ×ℝ) → ℝ)
    (f : (ℝ×ℝ) → ℂ) (hf : Differentiable ℝ f) (R : ℝ) (hR : 0<R) (z : ℝ×ℝ) :
    Tendsto (fun epsilon : ℝ => productSymmetricTruncation u epsilon R f z)
      (𝓝[>] 0) (𝓝 (productSlopePrincipalValue u R f z)) := by
  let g := fun t : ℝ => f (productSlopeSample u t z)-f (productSlopeSample u (-t) z)
  have hg : Differentiable ℝ g := by
    dsimp only [g,productSlopeSample]
    fun_prop
  have hg0 : g 0=0 := by simp [g,productSlopeSample]
  let reg := Function.update (fun t : ℝ => t⁻¹ • g t) 0 (deriv g 0)
  have hreg : Continuous reg := by
    apply continuous_iff_continuousAt.mpr
    intro t
    by_cases ht : t=0
    · subst t
      apply continuousAt_update_same.mpr
      simpa only [zero_add,hg0,sub_zero] using (hg 0).hasDerivAt.tendsto_slope_zero
    · apply (continuousAt_update_of_ne ht).mpr
      exact (continuousAt_id.inv₀ ht).smul hg.continuous.continuousAt
  have hcont : Continuous (fun epsilon : ℝ => ∫ t in epsilon..R, reg t) := by
    have hc := (intervalIntegral.continuous_primitive (μ:=volume)
      (fun l r => hreg.intervalIntegrable l r) R).neg
    have heq : (fun epsilon : ℝ => ∫ t in epsilon..R, reg t)=
        (fun epsilon : ℝ => -(∫ t in R..epsilon, reg t)) := by
      funext epsilon
      exact intervalIntegral.integral_symm R epsilon
    rw [heq]
    exact hc
  have heq : (fun epsilon : ℝ => productSymmetricTruncation u epsilon R f z)=ᶠ[𝓝[>] 0]
      (fun epsilon => ∫ t in epsilon..R, reg t) := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds]
      with epsilon he heR
    change 0<epsilon at he
    unfold productSymmetricTruncation
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le heR.le] at ht
    have ht0 : t≠0 := (he.trans_le ht.1).ne'
    exact (Function.update_of_ne ht0 (deriv g 0) (fun t : ℝ => t⁻¹ • g t)).symm
  exact (hcont.tendsto 0 |>.mono_left nhdsWithin_le_nhds).congr' heq.symm

theorem sharpSlope_eq_productSymmetric (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ)
    (hf : Continuous f) (epsilon R : ℝ) (he : 0<epsilon) (heR : epsilon≤R) (z : ℝ×ℝ) :
    slopeKernelOperator (sharpTimeKernel epsilon R) u f z=productSymmetricTruncation u epsilon R f z := by
  have h := sharpKernel_symmetrize epsilon R he heR (fun t => f (productSlopeSample u t z))
    (hf.comp (by unfold productSlopeSample; fun_prop))
  simpa only [slopeKernelOperator,productSlopeSample,productSymmetricTruncation,
    Complex.real_smul,Complex.ofReal_inv] using h

theorem sharp_shortTimeKernel (epsilon R : ℝ) (hR : R≤1/4) :
    shortTimeKernel (sharpTimeKernel epsilon R)=sharpTimeKernel epsilon R := by
  funext t
  unfold shortTimeKernel
  by_cases ht : |t|≤1/4
  · rw [ite_eq_left ht]
  · rw [ite_eq_right ht]
    symm
    unfold sharpTimeKernel
    rw [ite_eq_right (by intro h; exact ht (h.2.le.trans hR))]

theorem shortSharp_eq_productSymmetric (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ)
    (hf : Continuous f) (epsilon R : ℝ) (he : 0<epsilon) (heR : epsilon≤R) (hR : R≤1/4)
    (z : ℝ×ℝ) : shortSlopeOperator (sharpTimeKernel epsilon R) u f z=
      productSymmetricTruncation u epsilon R f z := by
  rw [shortSlopeOperator_eq_kernel,sharp_shortTimeKernel epsilon R hR]
  exact sharpSlope_eq_productSymmetric u f hf epsilon R he heR z

end LipschitzHilbert.PacketRepresentation

end

end OAI
