import OAI.Geometry.CylinderCovering.Angular.CubicRescaledDefinitions
import OAI.Geometry.CylinderCovering.Cubic.Contraction
import OAI.Geometry.CylinderCovering.Angular.CubicCost

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace CylinderCovering.Cubic
open TriangularCovering

lemma d_max_endpoints {a b : ℝ} (hab : a ≤ b) :
    IsGreatest (TriangularCovering.d '' Icc a b)
      (max (TriangularCovering.d a) (TriangularCovering.d b)) := by
  constructor
  · rcases le_total (TriangularCovering.d a) (TriangularCovering.d b) with h | h
    · rw [max_eq_right h]
      exact ⟨b, ⟨hab, le_rfl⟩, rfl⟩
    · rw [max_eq_left h]
      exact ⟨a, ⟨le_rfl, hab⟩, rfl⟩
  · rintro z ⟨q, hq, rfl⟩
    have h := profile_le_max_endpoints hq.1 hq.2
    change profile q ≤ profileMax a b at h
    rw [profile_eq_eight_d, profileMax_eq_eight_max_d] at h
    linarith

lemma scaled_cubicCost_bigO :
    (fun τ : ℝ => cubicCost (τ / 2) / (4 * H) - (1 / 2 - τ ^ 2 / 240))
      =O[𝓝[>] (0 : ℝ)] (fun τ => τ ^ 3) := by
  apply Asymptotics.IsBigO.of_bound (401 / 4)
  have hsmall : ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), τ < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with τ hτ hτ1
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ τ ^ 3 from pow_nonneg hτ.le 3)]
  exact scaled_cubicCost_expansion hτ hτ1.le

theorem fullCubicRescaled_proof : FullCubicRescaledStatement := by
  refine ⟨contraction_K4, (fun _ _ hab => d_max_endpoints hab), rescaled_cap,
    ?_, rescaledFiniteCover_proof, ?_, scaled_cubicCost_bigO,
    (1 / 50000 : ℝ), by norm_num, ?_⟩
  · have h : Tendsto (fun τ : ℝ => 25 / 4 * τ) (𝓝 (0 : ℝ)) (𝓝 (25 / 4 * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    simpa using h.mono_left nhdsWithin_le_nhds
  · intro τ hτ hτ1
    exact scaled_cubicCost_expansion hτ hτ1
  · intro τ hτ hτ1
    obtain ⟨_, C, hcover, harea, hprescribed⟩ :=
      rescaledFiniteCover_proof τ hτ (by linarith)
    refine ⟨C, hcover, hprescribed, harea, ?_⟩
    rw [harea, projection_minimum]
    have h := cubicCost_strict (show 0 < τ / 2 by linarith)
      (show τ / 2 ≤ 1 / 100000 by linarith)
    linarith

end CylinderCovering.Cubic

end

end OAI
