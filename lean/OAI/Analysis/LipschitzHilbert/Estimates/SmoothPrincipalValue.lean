import OAI.Analysis.LipschitzHilbert.Estimates.Truncation
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Pointwise symmetric principal values for smooth inputs. At a fixed
output point the direction is frozen, so differentiability of the input
removes the singularity in the positive-time symmetric quotient. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert

/-- The continuous extension at zero is integrated on the closed short
scale. The value at zero has no effect on the integral. -/
def smoothPrincipalValue (v : DirectionPlane → DirectionPlane) (a : ℝ)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) : ℂ :=
  let g := fun t : ℝ => f (sample v t x)-f (sample v (-t) x)
  ∫ t in (0:ℝ)..a, Function.update (fun t => t⁻¹ • g t) 0 (deriv g 0) t

theorem shortTransform_tendsto_smoothPrincipalValue
    (v : DirectionPlane → DirectionPlane) {f : DirectionPlane → ℂ}
    (hf : Differentiable ℝ f) {a : ℝ} (ha : 0 < a) (x : DirectionPlane) :
    Tendsto (fun ε : ℝ => shortTransform v ε a f x) (𝓝[>] 0)
      (𝓝 (smoothPrincipalValue v a f x)) := by
  let g := fun t : ℝ => f (sample v t x)-f (sample v (-t) x)
  have hg : Differentiable ℝ g := by
    dsimp only [g,sample]
    fun_prop
  have hg0 : g 0 = 0 := by simp [g,sample]
  let reg := Function.update (fun t : ℝ => t⁻¹ • g t) 0 (deriv g 0)
  have hreg : Continuous reg := by
    apply continuous_iff_continuousAt.mpr
    intro t
    by_cases ht : t = 0
    · subst t
      apply continuousAt_update_same.mpr
      simpa only [zero_add,hg0,sub_zero] using (hg 0).hasDerivAt.tendsto_slope_zero
    · apply (continuousAt_update_of_ne ht).mpr
      exact (continuousAt_id.inv₀ ht).smul hg.continuous.continuousAt
  have hcont : Continuous (fun ε : ℝ => ∫ t in ε..a, reg t) := by
    have hc := (intervalIntegral.continuous_primitive (μ := volume)
      (fun l r => hreg.intervalIntegrable l r) a).neg
    have he : (fun ε : ℝ => ∫ t in ε..a, reg t) =
        (fun ε : ℝ => -(∫ t in a..ε, reg t)) := by
      funext ε
      exact intervalIntegral.integral_symm a ε
    rw [he]
    exact hc
  have heq : (fun ε : ℝ => shortTransform v ε a f x) =ᶠ[𝓝[>] 0]
      (fun ε => ∫ t in ε..a, reg t) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with ε hε hεa
    change 0 < ε at hε
    unfold shortTransform
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hεa.le] at ht
    have ht0 : t ≠ 0 := (hε.trans_le ht.1).ne'
    exact (Function.update_of_ne ht0 (deriv g 0) (fun t : ℝ => t⁻¹ • g t)).symm
  exact (hcont.tendsto 0 |>.mono_left nhdsWithin_le_nhds).congr' heq.symm

theorem twoSidedTruncation_tendsto_smoothPrincipalValue
    (v : DirectionPlane → DirectionPlane) {f : DirectionPlane → ℂ}
    (hf : Differentiable ℝ f) {a : ℝ} (ha : 0 < a) (x : DirectionPlane) :
    Tendsto (fun ε : ℝ => twoSidedTruncation v ε a f x) (𝓝[>] 0)
      (𝓝 (smoothPrincipalValue v a f x)) := by
  apply (shortTransform_tendsto_smoothPrincipalValue v hf ha x).congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with ε hε hεa
  exact (twoSidedTruncation_eq_shortTransform v hf.continuous hε hεa.le x).symm

end LipschitzHilbert

end

end OAI
