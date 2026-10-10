import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Velocity
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Fluid

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory
open scoped BigOperators ContDiff Topology
namespace ShearFlows

theorem fderiv_translation {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} (hg : Differentiable ℝ g)
    {a : E} (ha : ∀ x, g (x + a) = g x) (x : E) :
    fderiv ℝ g (x + a) = fderiv ℝ g x := by
  have heq : (g ∘ fun y => y + a) = g := funext ha
  have hf := ((hg (x+a)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const a)).fderiv
  simpa only [id_eq, heq, ContinuousLinearMap.comp_id] using hf.symm

theorem mixedDerivative_smooth {V : Velocity} (hV : ContDiff ℝ ∞ V) :
    ∀ α, ContDiff ℝ ∞ (mixedDerivative V α) := by
  intro α
  induction α with
  | nil => exact hV
  | cons j α ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem mixedDerivative_spatially_periodic {V : Velocity} {L : ℝ}
    (hV : ContDiff ℝ ∞ V) (hp : SpatiallyPeriodic L V) :
    ∀ α, SpatiallyPeriodic L (mixedDerivative V α) := by
  intro α
  induction α with
  | nil => exact hp
  | cons j α ih =>
    intro t x n
    have ht (y : SpaceTime) : mixedDerivative V α (y + (0, latticeVector L n)) =
        mixedDerivative V α y := by simpa only [Prod.add_def, add_zero, zero_add, Prod.eta] using ih y.1 y.2 n
    simpa only [mixedDerivative, Prod.mk_add_mk, add_zero, zero_add] using
      congrArg (fun A : SpaceTime →L[ℝ] Space => A (spaceTimeDirection j))
      (fderiv_translation ((mixedDerivative_smooth hV α).differentiable (by simp)) ht (t,x))

theorem mixedDerivative_time_periodic {V : Velocity}
    (hV : ContDiff ℝ ∞ V) (hp : TimePeriodic V) :
    ∀ α, TimePeriodic (mixedDerivative V α) := by
  intro α
  induction α with
  | nil => exact hp
  | cons j α ih =>
    intro t x
    have ht (y : SpaceTime) : mixedDerivative V α (y + (1,0)) =
        mixedDerivative V α y := by simpa only [Prod.add_def, add_zero, zero_add, Prod.eta] using ih y.1 y.2
    simpa only [mixedDerivative, Prod.mk_add_mk, add_zero, zero_add] using
      congrArg (fun A : SpaceTime →L[ℝ] Space => A (spaceTimeDirection j))
      (fderiv_translation ((mixedDerivative_smooth hV α).differentiable (by simp)) ht (t,x))

theorem fundamentalCube_representative {L : ℝ} (hL : 0 < L) (x : Space) :
    ∃ y ∈ fundamentalCube L, ∃ n : Fin 3 → ℤ, x = y + latticeVector L n := by
  let n : Fin 3 → ℤ := fun j => ⌊x j / L⌋
  let y : Space := fun j => x j - L * (n j : ℝ)
  refine ⟨y, ⟨?_, ?_⟩, n, ?_⟩
  · intro j
    have h := (le_div_iff₀ hL).1 (Int.floor_le (x j / L))
    dsimp [y, n]
    nlinarith
  · intro j
    have h := (div_lt_iff₀ hL).1 (Int.lt_floor_add_one (x j / L))
    dsimp [y, n]
    nlinarith
  · ext j
    simp [y, latticeVector]

theorem periodic_uniform_bound {E : Type*} [NormedAddCommGroup E] {g : SpaceTime → E}
    {L : ℝ} (hL : 0 < L) (hc : Continuous g)
    (hs : SpatiallyPeriodic L g) (ht : TimePeriodic g) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖g y‖ ≤ B := by
  have hk : IsCompact (Icc (0 : ℝ) 1 ×ˢ fundamentalCube L) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hk.bddAbove_image hc.norm.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  rintro ⟨t,x⟩
  obtain ⟨y,hy,n,hx⟩ := fundamentalCube_representative hL x
  have htime : Function.Periodic (fun s => g (s,y)) 1 := fun s => ht s y
  have he : g (t,y) = g (t - (⌊t⌋ : ℝ),y) := by
    simpa using htime.int_mul ⌊t⌋ (t - (⌊t⌋ : ℝ))
  have hmem : (t - (⌊t⌋ : ℝ), y) ∈ Icc (0 : ℝ) 1 ×ˢ fundamentalCube L := by
    exact ⟨⟨sub_nonneg.mpr (Int.floor_le t), by linarith [Int.lt_floor_add_one t]⟩,hy⟩
  rw [hx, hs t y n, he]
  exact (hB (mem_image_of_mem _ hmem)).trans (le_max_left _ _)

theorem periodic_boundedMixedDerivatives {V : Velocity} {L : ℝ} (hL : 0 < L)
    (hV : ContDiff ℝ ∞ V) (hs : SpatiallyPeriodic L V) (ht : TimePeriodic V) :
    BoundedMixedDerivatives V := fun α => periodic_uniform_bound hL
      (mixedDerivative_smooth hV α).continuous
      (mixedDerivative_spatially_periodic hV hs α) (mixedDerivative_time_periodic hV ht α)

theorem realizingVelocity_boundedMixedDerivatives {d : Input} (hd : ValidInput d) :
    BoundedMixedDerivatives d.realizingVelocity :=
  periodic_boundedMixedDerivatives (by exact_mod_cast hd.period_pos)
    (realizingVelocity_smooth hd) (realizingVelocity_spatially_periodic d)
    (realizingVelocity_time_periodic d)

theorem realizingVelocity_kineticEnergy_bound {d : Input} (hd : ValidInput d) :
    ∃ B : ℝ, ∀ t, kineticEnergy d.period d.realizingVelocity t ≤ B :=
  kineticEnergy_uniform_bound (realizingVelocity_smooth hd).continuous
    (realizingVelocity_boundedMixedDerivatives hd) _

theorem spatialDerivative_eq_mixed {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (t : ℝ) (x : Space) (j : Fin 3) :
    derivative (fun y => V (t,y)) j x = mixedDerivative V [j.succ] (t,x) := by
  have hf := ((hV.differentiable (by simp) (t,x)).hasFDerivAt.comp x
    ((hasFDerivAt_const (c := t) x).prodMk (hasFDerivAt_id x))).fderiv
  change fderiv ℝ (fun y => V (t,y)) x (basis j) = fderiv ℝ V (t,x) (0,basis j)
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply] using congrArg (fun A => A (basis j)) hf

theorem laplacian_eq_mixed {V : Velocity} (hV : ContDiff ℝ ∞ V) (t : ℝ) (x : Space) :
    laplacian (fun y => V (t,y)) x = ∑ j : Fin 3, mixedDerivative V [j.succ,j.succ] (t,x) := by
  unfold laplacian
  apply Finset.sum_congr rfl
  intro j _
  have heq : derivative (fun y => V (t,y)) j = fun y => mixedDerivative V [j.succ] (t,y) :=
    funext (fun y => spatialDerivative_eq_mixed hV t y j)
  rw [heq]
  exact spatialDerivative_eq_mixed (mixedDerivative_smooth hV [j.succ]) t x j

theorem force_eq_mixed {V : Velocity} (hV : ContDiff ℝ ∞ V) (ν : ℝ) (y : SpaceTime) :
    force ν V y = mixedDerivative V [0] y - ν • ∑ j : Fin 3, mixedDerivative V [j.succ,j.succ] y := by
  rw [force, timeDerivative_eq hV, laplacian_eq_mixed hV]
  rfl

theorem force_spatially_periodic {V : Velocity} {L : ℝ} (hV : ContDiff ℝ ∞ V)
    (hp : SpatiallyPeriodic L V) (ν : ℝ) : SpatiallyPeriodic L (force ν V) := by
  intro t x n
  simp only [force_eq_mixed hV]
  rw [mixedDerivative_spatially_periodic hV hp [0] t x n]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  exact mixedDerivative_spatially_periodic hV hp [j.succ,j.succ] t x n

theorem force_time_periodic {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hp : TimePeriodic V) (ν : ℝ) : TimePeriodic (force ν V) := by
  intro t x
  simp only [force_eq_mixed hV]
  rw [mixedDerivative_time_periodic hV hp [0] t x]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  exact mixedDerivative_time_periodic hV hp [j.succ,j.succ] t x

theorem force_boundedMixedDerivatives {V : Velocity} {L : ℝ} (hL : 0 < L)
    (hV : ContDiff ℝ ∞ V) (hs : SpatiallyPeriodic L V) (ht : TimePeriodic V) (ν : ℝ) :
    BoundedMixedDerivatives (force ν V) :=
  periodic_boundedMixedDerivatives hL (force_smooth hV _)
    (force_spatially_periodic hV hs _) (force_time_periodic hV ht _)

theorem realizingVelocity_solves_NS {d : Input} (hd : ValidInput d) (ν : ℝ) :
    IsClassicalSolution d.period ν (force ν d.realizingVelocity) d.realizingVelocity (fun _ => 0) :=
  velocity_solves_forced_NS (realizingVelocity_smooth hd) (realizingVelocity_spatially_periodic d)
    (realizingVelocity_divergence_advection hd).1 (realizingVelocity_divergence_advection hd).2
    (fun x => realizingVelocity_vanish_near_integers d 0 (by norm_num) x) ν

end ShearFlows

end

end OAI
