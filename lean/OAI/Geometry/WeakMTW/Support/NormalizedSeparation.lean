import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology
namespace MovingTaylor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

 theorem normalized_separation_subseq {x q : ℕ → E} {x₀ : E}
    (_hx : Tendsto x atTop (𝓝 x₀)) (_hq : Tendsto q atTop (𝓝 x₀))
    (hne : ∀ᶠ j in atTop, q j ≠ x j) :
    ∃ e : E, ‖e‖ = 1 ∧ ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      Tendsto (fun j => NormedSpace.normalize (q (ρ j)-x (ρ j))) atTop (𝓝 e) := by
  have hb (j : ℕ) : NormedSpace.normalize (q j-x j) ∈ Metric.closedBall (0 : E) 1 := by
    rw [Metric.mem_closedBall,dist_zero_right]
    by_cases h : q j-x j = 0
    · simp [h]
    · rw [NormedSpace.norm_normalize h]
  obtain ⟨e,he,ρ,hρ,hlim⟩ := (isCompact_closedBall (0 : E) 1).tendsto_subseq hb
  refine ⟨e,?_,ρ,hρ,hlim⟩
  apply tendsto_nhds_unique hlim.norm
  apply tendsto_const_nhds.congr'
  filter_upwards [hρ.tendsto_atTop hne] with j hj
  exact (NormedSpace.norm_normalize (sub_ne_zero.mpr hj)).symm

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
 theorem separation_scale_limit {x q : ℕ → E} {x₀ : E}
    (hx : Tendsto x atTop (𝓝 x₀)) (hq : Tendsto q atTop (𝓝 x₀)) :
    Tendsto (fun j => ‖q j-x j‖) atTop (𝓝 0) := by
  simpa only [sub_self,norm_zero] using (hq.sub hx).norm

omit [FiniteDimensional ℝ E] in
 theorem separation_identity (x q : E) : x+‖q-x‖•NormedSpace.normalize (q-x) = q := by
  rw [NormedSpace.norm_smul_normalize,add_sub_cancel]

end MovingTaylor
end

end WeakMTWGlobalSupport

end OAI
