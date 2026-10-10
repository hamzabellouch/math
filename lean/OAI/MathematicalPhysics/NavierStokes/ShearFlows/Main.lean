import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Trajectories
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ClassicalUniqueness
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ForceEvaluation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory
open scoped BigOperators Topology ContDiff
namespace ShearFlows

def ForcedFluidProperties (d : Input) (c : FinitePrescription) (V : Velocity) : Prop :=
  (∃ B : ℝ, ∀ t, kineticEnergy d.period V t ≤ B) ∧
  ∀ ν : ℝ, 0 < ν → ComputableReal ν →
    ContDiff ℝ ∞ (force ν V) ∧
    SpatiallyPeriodic d.period (force ν V) ∧
    HasZeroMean d.period (force ν V) ∧ Solenoidal (force ν V) ∧
    TimePeriodic (force ν V) ∧ BoundedMixedDerivatives (force ν V) ∧
    HasEffectiveForce ν V c.code ∧
    IsClassicalSolution d.period ν (force ν V) V (fun _ => 0) ∧
    (∀ u p, IsClassicalSolution d.period ν (force ν V) u p →
      ∀ t, 0 ≤ t → ∀ x, u (t, x) = V (t, x) ∧ p (t, x) = 0)

structure Realization (d : Input) (c : FinitePrescription) (V : Velocity)
    (Φ : ℝ → Space → Space) (s : Schedule) : Prop where
  smooth : ContDiff ℝ ∞ V
  spatially_periodic : SpatiallyPeriodic d.period V
  time_periodic : TimePeriodic V
  vanishes_near_integers : ∃ ε : ℚ, 0 < ε ∧
    ∀ k : ℤ, ∀ t : ℝ, |t - (k : ℝ)| < (ε : ℝ) → ∀ x, V (t, x) = 0
  effective_derivatives : HasEffectiveDerivatives V c.code
  bounded_derivatives : BoundedMixedDerivatives V
  divergence_zero : Solenoidal V
  mean_zero : HasZeroMean d.period V
  advection_zero : ZeroAdvection V
  flow : IsMaterialFlow d.period V Φ
  radius_pos : 0 < c.radius
  tube_in_chart : ∀ b ∈ d.instructions,
    sourceTube b d.codingHeight c.radius ⊆ d.inChart
  tube_open : ∀ b ∈ d.instructions, IsOpen (sourceTube b d.codingHeight c.radius)
  tube_contains : ∀ b ∈ d.instructions,
    (fun X => atHeight X d.codingHeight) '' b.source.carrier ⊆ sourceTube b d.codingHeight c.radius
  period_map : ∀ b ∈ d.instructions,
    ∀ x ∈ sourceTube b d.codingHeight c.radius,
      Φ 1 x = atHeight (b.affine (horizontal x)) (x 2)
  stages : StageMotion d Φ s
  gaps : ∀ t ∈ Icc (0 : ℝ) 1,
    (∀ j, t ∉ Ioo (s.start j : ℝ) (s.finish j : ℝ)) → ∀ x, V (t, x) = 0
  fluid : ForcedFluidProperties d c V
  empty_zero : d.instructions = [] → V = 0

theorem sourceTube_open (b : Instruction) (z δ : ℝ) : IsOpen (sourceTube b z δ) := by
  have hh : Continuous horizontal := by
    apply continuous_pi
    intro j
    fin_cases j <;> exact continuous_apply _
  have he : sourceTube b z δ = ⋃ y ∈ b.source.carrier,
      {x : Space | ‖horizontal x - y‖ < δ ∧ |x 2-z| < δ} := by
    ext x
    simp only [sourceTube, mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [he]
  apply isOpen_biUnion
  intro y _
  exact (isOpen_lt (hh.sub continuous_const).norm continuous_const).inter
    (isOpen_lt ((continuous_apply 2).sub continuous_const).abs continuous_const)

theorem sourceTube_contains (b : Instruction) (z : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (fun X => atHeight X z) '' b.source.carrier ⊆ sourceTube b z δ := by
  rintro x ⟨X,hX,rfl⟩
  refine ⟨X,hX,?_,?_⟩
  · simpa only [atHeight_horizontal, sub_self, norm_zero] using hδ
  · simpa [atHeight] using hδ

theorem realizingVelocity_fluid {d : Input} (hd : ValidInput d) :
    ForcedFluidProperties d (compileShears d) d.realizingVelocity := by
  refine ⟨realizingVelocity_kineticEnergy_bound hd, ?_⟩
  intro ν hν _
  exact ⟨force_smooth (realizingVelocity_smooth hd) ν,
    force_spatially_periodic (realizingVelocity_smooth hd) (realizingVelocity_spatially_periodic d) ν,
    realizingForce_mean_zero hd ν,
    force_solenoidal (realizingVelocity_smooth hd) (realizingVelocity_divergence_advection hd).1 ν,
    force_time_periodic (realizingVelocity_smooth hd) (realizingVelocity_time_periodic d) ν,
    force_boundedMixedDerivatives (by exact_mod_cast hd.period_pos)
      (realizingVelocity_smooth hd) (realizingVelocity_spatially_periodic d)
      (realizingVelocity_time_periodic d) ν,
    compileShears_force_effective hd ν, realizingVelocity_solves_NS hd ν,
    realizingVelocity_unique hd hν⟩

theorem reciprocal_affine_maps_by_shears :
    ∀ d : Input, ValidInput d →
      ∃ (V : Velocity) (Φ : ℝ → Space → Space) (s : Schedule),
        Realization d (compileShears d) V Φ s := by
  intro d hd
  obtain ⟨Φ,hΦ⟩ := realizingVelocity_materialFlow hd
  refine ⟨d.realizingVelocity, Φ, standardSchedule, ?_⟩
  exact {
    smooth := realizingVelocity_smooth hd
    spatially_periodic := realizingVelocity_spatially_periodic d
    time_periodic := realizingVelocity_time_periodic d
    vanishes_near_integers := ⟨1/32, by norm_num, fun k t ht x =>
      realizingVelocity_vanish_near_integers d k (by norm_num at ht ⊢; exact ht) x⟩
    effective_derivatives := compileShears_effective hd
    bounded_derivatives := realizingVelocity_boundedMixedDerivatives hd
    divergence_zero := (realizingVelocity_divergence_advection hd).1
    mean_zero := realizingVelocity_mean_zero hd
    advection_zero := (realizingVelocity_divergence_advection hd).2
    flow := hΦ
    radius_pos := tubeRadius_pos hd
    tube_in_chart := fun b hb => sourceTube_in_chart hd hb
    tube_open := fun b _ => sourceTube_open b _ _
    tube_contains := fun b _ => sourceTube_contains b _ (by exact_mod_cast tubeRadius_pos hd)
    period_map := fun b hb x hx => realizingVelocity_periodMap hd hΦ hb hx
    stages := realizingVelocity_stages hd hΦ
    gaps := fun t ht hg x => realizingVelocity_gaps d ht hg x
    fluid := realizingVelocity_fluid hd
    empty_zero := realizingVelocity_empty d }

end ShearFlows

end

end OAI
