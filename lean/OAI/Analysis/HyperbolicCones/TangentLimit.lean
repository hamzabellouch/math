import OAI.Analysis.HyperbolicCones.Model

namespace OAI

noncomputable section

open scoped Topology
open Filter

universe u

namespace Paper256

theorem norm_sq_derivative_of_quadratic_curve
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (v : F) (α β : ℝ) (hβ : 0 ≤ β)
    (hf : HasDerivAt f v 0) (hzero : f 0 = 0)
    (hval : ∀ s : ℝ, ‖f s‖ ^ 2 = s ^ 2 / (1 + s ^ 2 * β) * α) :
    ‖v‖ ^ 2 = α := by
  have ht : Tendsto (fun s : ℝ => ‖s⁻¹ • f s‖ ^ 2) (𝓝[≠] 0) (𝓝 (‖v‖ ^ 2)) := by
    simpa only [zero_add, hzero, sub_zero] using hf.tendsto_slope_zero.norm.pow 2
  have hc : ContinuousAt (fun s : ℝ => α / (1 + s ^ 2 * β)) 0 := by
    fun_prop (disch := norm_num)
  have hr : Tendsto (fun s : ℝ => α / (1 + s ^ 2 * β)) (𝓝[≠] 0) (𝓝 α) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have he : (fun s : ℝ => ‖s⁻¹ • f s‖ ^ 2) =ᶠ[𝓝[≠] 0]
      (fun s : ℝ => α / (1 + s ^ 2 * β)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := hs
    have hd : 1 + s ^ 2 * β ≠ 0 := ne_of_gt (by positivity)
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hval]
    field_simp
  exact tendsto_nhds_unique ht (hr.congr' he.symm)

end Paper256

end

end OAI
