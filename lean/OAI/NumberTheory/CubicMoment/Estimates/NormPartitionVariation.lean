import OAI.NumberTheory.CubicMoment.Estimates.SmoothNormPartition
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace OAI

/-! Uniform scaled derivative bounds for the actual distinguished norm
partition. Rescaling the prime norm introduces no growing variation cost. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma normPartitionWeight_deriv_zero {x : ℝ} (hx : x ∉ Icc (1:ℝ) 2) :
    deriv normPartitionWeight x = 0 := by
  by_cases hlo : x < 1
  · have he : EqOn normPartitionWeight (fun _ : ℝ => (0:ℂ)) (Iio 1) :=
      fun _ hy => normPartitionWeight_low hy
    simpa only [deriv_const] using he.deriv isOpen_Iio hlo
  · have hhi : 2 < x := by
      rcases not_and_or.mp hx with h | h
      · exact False.elim (h (le_of_not_gt hlo))
      · exact lt_of_not_ge h
    have he : EqOn normPartitionWeight (fun _ : ℝ => (0:ℂ)) (Ioi 2) :=
      fun _ hy => normPartitionWeight_high hy
    simpa only [deriv_const] using he.deriv isOpen_Ioi hhi

theorem normPartitionWeight_radial_deriv_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 0 < x → ‖deriv normPartitionWeight x‖*x ≤ D := by
  have hd : Continuous (deriv normPartitionWeight) :=
    normPartitionWeight_smooth.continuous_deriv (by norm_num)
  obtain ⟨D,hD⟩ := (isCompact_Icc (a := (1:ℝ)) (b := 2)).exists_bound_of_continuousOn
    ((hd.norm.mul continuous_id).continuousOn)
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro x hx
  by_cases hmem : x ∈ Icc (1:ℝ) 2
  · have h := hD x hmem
    change ‖‖deriv normPartitionWeight x‖*x‖ ≤ D at h
    rw [Real.norm_of_nonneg (mul_nonneg (_root_.norm_nonneg _) hx.le)] at h
    exact h.trans (le_max_left _ _)
  · rw [normPartitionWeight_deriv_zero hmem,norm_zero,zero_mul]
    exact le_max_right _ _

def scaledNormPartitionWeight (c x : ℝ) : ℂ := normPartitionWeight (c*x)

lemma scaledNormPartitionWeight_smooth (c : ℝ) :
    ContDiff ℝ ∞ (scaledNormPartitionWeight c) :=
  normPartitionWeight_smooth.comp (contDiff_const.mul contDiff_id)

lemma scaledNormPartitionWeight_norm (c x : ℝ) : ‖scaledNormPartitionWeight c x‖ ≤ 1 :=
  normPartitionWeight_norm _

theorem scaledNormPartitionWeight_deriv_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ c : ℝ, 0 < c → ∀ x : ℝ, 0 < x →
      ‖deriv (scaledNormPartitionWeight c) x‖*x ≤ D := by
  obtain ⟨D,hD,hbound⟩ := normPartitionWeight_radial_deriv_bound
  refine ⟨D,hD,?_⟩
  intro c hc x hx
  have hd := ((normPartitionWeight_smooth.differentiable (by norm_num)).differentiableAt
    (x := c*x)).hasDerivAt.scomp x (hasDerivAt_const_mul c)
  have he : deriv (scaledNormPartitionWeight c) x = c • deriv normPartitionWeight (c*x) := hd.deriv
  rw [he,norm_smul,Real.norm_of_nonneg hc.le]
  calc
    _ = ‖deriv normPartitionWeight (c*x)‖*(c*x) := by ring
    _ ≤ D := hbound _ (mul_pos hc hx)

end CubicFirstMoment

end

end OAI
