import Mathlib

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
namespace TamingCompatibility

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem bilinear_coercive_of_pos (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v, v ≠ 0 → 0 < B v v) : IsCoercive B := by
  have hc : Continuous (fun v : E => B v v) := B.continuous.clm_apply continuous_id
  obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hc.continuousOn
  have hv₀norm : ‖v₀‖ = 1 := by simpa using hv₀
  have hv₀ne : v₀ ≠ 0 := by intro h; simp [h] at hv₀norm
  refine ⟨B v₀ v₀, hB v₀ hv₀ne, ?_⟩
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u : E := ‖v‖⁻¹ • v
  have hun : ‖u‖ = 1 := by simp [u, norm_smul, hn.ne']
  have hu : u ∈ Metric.sphere (0 : E) 1 := by simpa using hun
  have hm := hmin hu
  have heq : B v v = ‖v‖ ^ 2 * B u u := by
    dsimp [u]
    simp only [map_smul, _root_.smul_apply, smul_eq_mul]
    field_simp
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left hm (sq_nonneg ‖v‖)]

theorem bilinear_unitBall_isVonNBounded (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v, v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v | B v v < 1} := by
  obtain ⟨c, hc, hco⟩ := bilinear_coercive_of_pos B hB
  apply (NormedSpace.isVonNBounded_ball ℝ E (1 / c + 1)).subset
  intro v hv
  rw [Metric.mem_ball, dist_zero_right]
  have hmul : c * (1 / c) = 1 := by field_simp
  by_contra! hn
  have hrec : 0 < 1 / c := one_div_pos.mpr hc
  have hn1 : 1 < ‖v‖ := by linarith
  have hnpos : 0 < ‖v‖ := hn1.trans' zero_lt_one
  have hcn : 1 < c * ‖v‖ := by nlinarith
  have hsq : c * ‖v‖ ≤ c * ‖v‖ ^ 2 := by nlinarith
  have hco' := hco v
  change B v v < 1 at hv
  linarith

end TamingCompatibility

end

end OAI
