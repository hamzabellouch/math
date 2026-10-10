import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowForce
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.MixedOrdering

namespace OAI

/-! Square integrability on the torus follows from the actual inverse-time
bound, for every mixed derivative of the initialized slow force. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
open ShearFlows

namespace ForcedComputation

def TorusMixedL2 (L : ℝ) (F : Velocity) : Prop :=
  ∀ α, MemLp (mixedDerivative F α) 2
    (volume.restrict (Ici (0 : ℝ) ×ˢ fundamentalCube L))

theorem inverse_time_memLp : MemLp (fun t : ℝ => (1 + t)⁻¹) 2
    (volume.restrict (Ici (0 : ℝ))) := by
  have hc : ContinuousOn (fun t : ℝ => (1 + t)⁻¹) (Ici (0 : ℝ)) := by
    apply ContinuousOn.inv₀ (continuous_const.add continuous_id).continuousOn
    intro t ht
    change 1 + t ≠ 0
    have ht0 : 0 ≤ t := ht
    linarith
  apply (memLp_two_iff_integrable_sq (hc.aestronglyMeasurable measurableSet_Ici)).mpr
  apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
  have hi : IntegrableOn (fun t : ℝ => (t + 1) ^ (-2 : ℝ)) (Ioi (0 : ℝ)) :=
    integrableOn_add_rpow_Ioi_of_lt (by norm_num) (by norm_num)
  apply hi.congr_fun _ measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := ht
  change (t + 1) ^ (-2 : ℝ) = ((1 + t)⁻¹) ^ 2
  rw [Real.rpow_neg (by linarith [ht0] : 0 ≤ t + 1),
    show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, Real.rpow_natCast, inv_pow, add_comm]

theorem torus_memLp_of_inverse_bound (L : ℝ) {F : Velocity} (hc : Continuous F)
    {C : ℝ} (hb : ∀ t, 0 ≤ t → ∀ x, ‖F (t, x)‖ ≤ C * (1 + t)⁻¹) :
    MemLp F 2 (volume.restrict (Ici (0 : ℝ) ×ˢ fundamentalCube L)) := by
  let : IsFiniteMeasure (volume.restrict (fundamentalCube L)) :=
    isFiniteMeasure_restrict.mpr isCompact_Icc.measure_ne_top
  have hg := inverse_time_memLp.comp_fst (volume.restrict (fundamentalCube L))
  rw [Measure.prod_restrict] at hg
  apply hg.of_le_mul (c := C) hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)] with y hy
  have ht0 : 0 ≤ y.1 := hy.1
  have hi : 0 ≤ (1 + y.1)⁻¹ := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hi] using hb y.1 ht0 y.2

theorem slowFromRest_force_mixed_bound {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    (hb : BoundedMixedDerivatives V) (ha : ZeroAdvection V) (ν : ℝ)
    (α : List (Fin 4)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → ∀ x,
      ‖mixedDerivative (force ν (slowFromRest V)) α (t, x)‖ ≤ C * (1 + t)⁻¹ := by
  have hs := force_smooth (slowFromRest_smooth hV hzero) ν
  obtain ⟨n, β, hp⟩ := time_spatial_normal_form α
  obtain ⟨C, hC, hbound⟩ := slowFromRest_force_spatial_time_decay hV hzero hb ha ν β n
  refine ⟨C, hC, fun t ht x => ?_⟩
  rw [mixedDerivative_perm hs hp, mixedDerivative_time_spatial hs]
  apply (hbound x t ht).trans
  apply mul_le_mul_of_nonneg_left _ hC
  have hp0 : 0 ≤ (1 + t)⁻¹ := by positivity
  have hp1 : (1 + t)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith : 0 < 1 + t)).mpr (by linarith)
  rw [pow_add, pow_one]
  exact mul_le_of_le_one_right hp0 (pow_le_one₀ hp0 hp1)

theorem slowFromRest_force_L2 {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    (hb : BoundedMixedDerivatives V) (ha : ZeroAdvection V) (ν L : ℝ) :
    TorusMixedL2 L (force ν (slowFromRest V)) := by
  intro α
  obtain ⟨C, _, hC⟩ := slowFromRest_force_mixed_bound hV hzero hb ha ν α
  exact torus_memLp_of_inverse_bound L
    (mixedDerivative_smooth (force_smooth (slowFromRest_smooth hV hzero) ν) α).continuous hC

end ForcedComputation

end

end OAI
