import OAI.MeasureTheory.Falconer.Recursion.ParentConeSource
import OAI.MeasureTheory.Falconer.Angular.SmoothRotatedCone

namespace OAI

namespace PlanarFalconer
open Set Filter
open scoped ContDiff Topology

theorem sourceConeCircle_zero_of_cos_neg (axis θ : ℝ)
    (hc : Real.cos (θ-axis) < 0) : sourceConeCircle axis (sourceUnitDirection θ) = 0 := by
  by_contra hn
  have hs : sourceAngle (sourceUnitDirection (θ-axis)) ∈ Icc (-1/5:ℝ) (1/5) := by
    apply graphConeCutoff_support
    apply subset_closure
    simpa only [Function.mem_support,sourceConeCircle,sourceCircleRotate_comp,
      sub_eq_add_neg] using hn
  have hcos : 0 ≤ Real.cos (sourceAngle (sourceUnitDirection (θ-axis))) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith only [hs.1, Real.one_le_pi_div_two])
      (by linarith only [hs.2, Real.one_le_pi_div_two])
  rw [periodic_sourceAngle Real.cos_periodic] at hcos
  exact (not_lt_of_ge hcos) hc

theorem sourceConeCircle_inverse_germs (axis : ℝ) {φ : ℝ} (hφ : |φ| ≤ 1/20) :
    (fun θ => sourceConeCircle axis (sourceUnitDirection θ)) =ᶠ[𝓝 (φ+axis)] (fun _ => 1) ∧
    (fun θ => sourceConeCircle axis (sourceUnitDirection θ)) =ᶠ[𝓝 (φ+axis+Real.pi)] (fun _ => 0) := by
  constructor
  · filter_upwards [Metric.ball_mem_nhds (φ+axis) (by norm_num : (0:ℝ) < 1/20)] with θ hθ
    have hh : |(θ-axis)-φ| ≤ 1/20 := by
      rw [Metric.mem_ball,Real.dist_eq] at hθ
      convert hθ.le using 1
      congr 1
      ring
    simpa using sourceConeCircle_one_near_centered_angle axis hφ hh
  · have hc : Real.cos (φ+axis+Real.pi-axis) < 0 := by
      have hp : -(Real.pi/2) < φ ∧ φ < Real.pi/2 := by
        have hh := abs_le.mp hφ
        constructor
        · linarith only [hh.1, Real.pi_gt_three]
        · linarith only [hh.2, Real.pi_gt_three]
      rw [show φ+axis+Real.pi-axis = φ+Real.pi by ring,Real.cos_add_pi]
      exact neg_neg_of_pos (Real.cos_pos_of_mem_Ioo hp)
    have hne : {θ : ℝ | Real.cos (θ-axis) < 0} ∈ 𝓝 (φ+axis+Real.pi) :=
      (isOpen_lt (Real.continuous_cos.comp (continuous_id.sub continuous_const))
        continuous_const).mem_nhds hc
    filter_upwards [hne] with θ hθ
    exact sourceConeCircle_zero_of_cos_neg axis θ hθ

theorem sourceConeCircle_uniform_derivatives (n : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ axis : ℝ, ∀ j ≤ n, ∀ θ,
      ‖iteratedDeriv j (fun t => sourceConeCircle axis (sourceUnitDirection t)) θ‖ ≤ P := by
  let f := fun θ => sourceConeCircle 0 (sourceUnitDirection θ)
  have hf : ContDiff ℝ ∞ f := sourceConeCircle_angular_contDiff
  have hp : Function.Periodic f (2*Real.pi) :=
    fun θ => congrArg (sourceConeCircle 0) (sourceUnitDirection_periodic θ)
  have hj (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ θ, ‖iteratedDeriv j f θ‖ ≤ B := by
    have hpj : Function.Periodic (iteratedDeriv j f) (2*Real.pi) := by
      have he : (fun x => f (x+2*Real.pi)) = f := funext hp
      have hh := iteratedDeriv_comp_add_const j f (2*Real.pi)
      rw [he] at hh
      intro x
      exact (congrFun hh x).symm
    obtain ⟨B,hB⟩ := (hpj.isBounded_of_continuous
      (by positivity : 2*Real.pi ≠ 0) (hf.continuous_iteratedDeriv j
        (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤)))).exists_norm_le
    exact ⟨max 0 B,le_max_left _ _,fun θ => (hB _ ⟨θ,rfl⟩).trans (le_max_right _ _)⟩
  choose B hB hb using hj
  refine ⟨∑ j ∈ Finset.range (n+1), B j,Finset.sum_nonneg (fun j _ => hB j),?_⟩
  intro axis j hj θ
  rw [sourceConeCircle_rotated_deriv]
  exact (hb j (θ-axis)).trans (Finset.single_le_sum (fun k _ => hB k)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

end PlanarFalconer

end OAI
