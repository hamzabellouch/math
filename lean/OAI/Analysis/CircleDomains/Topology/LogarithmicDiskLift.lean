import OAI.Analysis.CircleDomains.Selection.RayProjection
import OAI.Analysis.CircleDomains.Topology.CircleLifts

namespace OAI

/-! Actual continuous logarithmic lifts on simply connected physical
patches. The real coordinate is obtained from the existing circle cover. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_logarithmic_disk_lift {U : Set ℂ}
    [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    (w : ℂ → ℂ) (hw : ContinuousOn w U)
    (hw0 : ∀ z ∈ U, w z ≠ 0) (hw1 : ∀ z ∈ U, ‖w z‖ ≤ 1)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ Ψ : ℂ → ℂ, ContinuousOn Ψ U ∧
      (∀ z ∈ U, 0 ≤ (Ψ z).im) ∧
      ∀ z ∈ U, diskRayProjection (Ψ z) = w z := by
  have harg : ContinuousOn (normalizedArgument ∘ w) U := fun z hz =>
    (continuousAt_normalizedArgument (hw0 z hz)).comp_continuousWithinAt (hw z hz)
  obtain ⟨r, _, hr⟩ := AddCircle.eq_coe_Ico (normalizedArgument (w z₀))
  obtain ⟨u, hu, _, hproj⟩ := exists_continuous_circle_lift (normalizedArgument ∘ w) harg hz₀ r hr
  let Ψ : ℂ → ℂ := fun z => (u z : ℂ) + ((-Real.log ‖w z‖ : ℝ) : ℂ) * Complex.I
  have him (z : ℂ) : (Ψ z).im = -Real.log ‖w z‖ := by simp [Ψ]
  have hre (z : ℂ) : (Ψ z).re = u z := by simp [Ψ]
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · exact (Complex.continuous_ofReal.comp_continuousOn hu).add
      ((Complex.continuous_ofReal.comp_continuousOn
        ((hw.norm.log (fun z hz => norm_ne_zero_iff.mpr (hw0 z hz))).neg)).mul_const _)
  · intro z hz
    rw [him]
    exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (hw1 z hz))
  · intro z hz
    apply Complex.ext_norm_arg
    · rw [diskRayProjection_norm, him, neg_neg,
        Real.exp_log (norm_pos_iff.mpr (hw0 z hz))]
    · apply Complex.arg_coe_angle_eq_iff.mp
      apply (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective
      change normalizedArgument (diskRayProjection (Ψ z)) = normalizedArgument (w z)
      rw [diskRayProjection_argument, hre]
      exact hproj z hz

 theorem exists_logarithmic_disk_lift_ball (w : ℂ → ℂ) {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hw : ContinuousOn w (Metric.ball z₀ r))
    (hw0 : ∀ z ∈ Metric.ball z₀ r, w z ≠ 0)
    (hw1 : ∀ z ∈ Metric.ball z₀ r, ‖w z‖ ≤ 1) :
    ∃ Ψ : ℂ → ℂ, ContinuousOn Ψ (Metric.ball z₀ r) ∧
      (∀ z ∈ Metric.ball z₀ r, 0 ≤ (Ψ z).im) ∧
      ∀ z ∈ Metric.ball z₀ r, diskRayProjection (Ψ z) = w z := by
  let : ContractibleSpace (Metric.ball z₀ r) :=
    (convex_ball z₀ r).contractibleSpace (Metric.nonempty_ball.mpr hr)
  let : LocallyPathConnectedSpace (Metric.ball z₀ r) := Metric.isOpen_ball.locallyPathConnectedSpace
  exact exists_logarithmic_disk_lift w hw hw0 hw1 (Metric.mem_ball_self hr)

end CircleDomainRigidity

end

end OAI
