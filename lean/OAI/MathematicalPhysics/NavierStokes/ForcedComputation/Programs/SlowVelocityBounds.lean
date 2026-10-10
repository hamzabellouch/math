import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowIntegrability

namespace OAI

/-! Uniform-in-space, square-integrable-in-time bounds for both the slowed
velocity and its force. These imply the time-supremum norm bounds in the
fixed-particle theorem, not just space-time integrability. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
open ShearFlows

namespace ForcedComputation

def UniformMixedL2 (V : Velocity) : Prop :=
  letI := ShearFlows.twoAtLeastTwo
  ∀ α, ∃ g : ℝ → ℝ, MemLp g 2 (volume.restrict (Ici (0 : ℝ))) ∧
    (∃ C : ℝ, ∀ t, 0 ≤ t → g t ≤ C) ∧
    ∀ t, 0 ≤ t → ∀ x, ‖mixedDerivative V α (t, x)‖ ≤ g t

theorem uniformMixedL2_of_inverse_bound {V : Velocity}
    (h : ∀ α, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → ∀ x,
      ‖mixedDerivative V α (t, x)‖ ≤ C * (1 + t)⁻¹) : UniformMixedL2 V := by
  intro α
  obtain ⟨C, hC, hbound⟩ := h α
  refine ⟨fun t => C * (1 + t)⁻¹, inverse_time_memLp.const_mul C, ⟨C, ?_⟩, hbound⟩
  intro t ht
  have hi : (1 + t)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith : 0 < 1 + t)).mpr (by linarith)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hi hC

theorem slowFromRest_spatial_time_decay {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    (hb : BoundedMixedDerivatives V) (α : List (Fin 3)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, 0 ≤ t →
      ‖iteratedDeriv n (fun s => spatialWord α
        (fun y => slowFromRest V (s, y)) x) t‖ ≤ C * (1 + t)⁻¹ ^ (1 + n) := by
  obtain ⟨C, hC, hbound⟩ := bounded_profile_mixed_decay hV hb 1 n α
  refine ⟨C, hC, fun x t ht => ?_⟩
  have he : (fun s => spatialWord α (fun y => slowFromRest V (s, y)) x)
      =ᶠ[𝓝 t] fun s => spatialWord α
        (fun y => logarithmicProfile 1 (fun q => V (q, y)) s) x := by
    filter_upwards [eventually_gt_nhds (show -(1 / 2 : ℝ) < t by linarith)] with s hs
    have hf : (fun y => slowFromRest V (s, y)) =
        fun y => logarithmicProfile 1 (fun q => V (q, y)) s := by
      funext y
      rw [slowFromRest_eq_near_nonnegative hzero hs]
      simp only [slowVelocity, reparametrizedVelocity, logarithmicProfile, logClock, pow_one]
    rw [hf]
  rw [he.iteratedDeriv_eq n]
  exact hbound x t ht

theorem slowFromRest_mixed_bound {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    (hb : BoundedMixedDerivatives V) (α : List (Fin 4)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → ∀ x,
      ‖mixedDerivative (slowFromRest V) α (t, x)‖ ≤ C * (1 + t)⁻¹ := by
  have hs := slowFromRest_smooth hV hzero
  obtain ⟨n, β, hp⟩ := time_spatial_normal_form α
  obtain ⟨C, hC, hbound⟩ := slowFromRest_spatial_time_decay hV hzero hb β n
  refine ⟨C, hC, fun t ht x => ?_⟩
  rw [mixedDerivative_perm hs hp, mixedDerivative_time_spatial hs]
  apply (hbound x t ht).trans
  apply mul_le_mul_of_nonneg_left _ hC
  have hp0 : 0 ≤ (1 + t)⁻¹ := by positivity
  have hp1 : (1 + t)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith : 0 < 1 + t)).mpr (by linarith)
  rw [pow_add, pow_one]
  exact mul_le_of_le_one_right hp0 (pow_le_one₀ hp0 hp1)

theorem slowFromRest_uniformMixedL2 {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    (hb : BoundedMixedDerivatives V) (ha : ZeroAdvection V) (ν : ℝ) :
    UniformMixedL2 (slowFromRest V) ∧ UniformMixedL2 (force ν (slowFromRest V)) :=
  ⟨uniformMixedL2_of_inverse_bound (slowFromRest_mixed_bound hV hzero hb),
    uniformMixedL2_of_inverse_bound (slowFromRest_force_mixed_bound hV hzero hb ha ν)⟩

end ForcedComputation

end

end OAI
