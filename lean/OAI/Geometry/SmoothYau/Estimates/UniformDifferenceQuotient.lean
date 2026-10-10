import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology BoundedContinuousFunction
namespace YauCounterexamples
variable {X F : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem uniform_difference_quotient (f d : ℝ → X → F)
    (hd : Continuous (fun z : ℝ × X => d z.1 z.2))
    (hf : ∀ t x, HasDerivAt (fun r => f r x) (d t x) t) :
    TendstoUniformly (fun t x => t⁻¹ • (f t x-f 0 x)) (d 0) (𝓝[≠] (0 : ℝ)) := by
  let : UniformSpace X := uniformSpaceOfCompactR1
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hu := Continuous.tendstoUniformly d hd 0
  have he := (Metric.tendstoUniformly_iff.mp hu) (ε/2) (by positivity)
  obtain ⟨δ,hδ,hδe⟩ := Metric.mem_nhds_iff.mp he
  have htball : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Metric.ball 0 δ := Metric.ball_mem_nhds 0 hδ
  have ht : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ∈ Metric.ball 0 δ ∧ t ≠ 0 :=
    (htball.filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  filter_upwards [ht] with t ht
  intro x
  have hder (r : ℝ) : HasDerivAt (fun r => f r x-r • d 0 x) (d r x-d 0 x) r := by
    simpa only [id_eq,one_smul,Pi.sub_apply] using! (hf r x).sub ((hasDerivAt_id r).smul_const (d 0 x))
  have hb (r : ℝ) (hr : r ∈ Metric.ball 0 δ) : ‖d r x-d 0 x‖ ≤ ε/2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using (hδe hr x).le
  have hm := (convex_ball (0 : ℝ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (hder r).hasDerivWithinAt) hb (Metric.mem_ball_self hδ) ht.1
  have hm' : ‖f t x-f 0 x-t • d 0 x‖ ≤ (ε/2)*‖t‖ := by
    simpa only [zero_smul, sub_zero, sub_right_comm] using hm
  have heq : t⁻¹ • (f t x-f 0 x)-d 0 x =
      t⁻¹ • (f t x-f 0 x-t • d 0 x) := by
    symm
    rw [smul_sub,smul_smul,inv_mul_cancel₀ ht.2,one_smul]
  rw [dist_eq_norm,norm_sub_rev,heq,norm_smul]
  calc
    ‖t⁻¹‖ * ‖f t x-f 0 x-t • d 0 x‖ ≤ ‖t⁻¹‖*((ε/2)*‖t‖) :=
      mul_le_mul_of_nonneg_left hm' (norm_nonneg _)
    _ = (ε/2)*(‖t‖⁻¹*‖t‖) := by rw [norm_inv]; ring
    _ = ε/2 := by rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr ht.2),mul_one]
    _ < ε := half_lt_self hε

theorem bounded_difference_quotient (f d : ℝ → X →ᵇ F)
    (hd : Continuous (fun z : ℝ × X => d z.1 z.2))
    (hf : ∀ t x, HasDerivAt (fun r => f r x) (d t x) t) :
    Tendsto (fun t => t⁻¹ • (f t-f 0)) (𝓝[≠] (0 : ℝ)) (𝓝 (d 0)) := by
  rw [BoundedContinuousFunction.tendsto_iff_tendstoUniformly]
  exact uniform_difference_quotient (fun t x => f t x) (fun t x => d t x) hd hf
end YauCounterexamples
end

end OAI
