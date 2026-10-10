import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedLoader
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.StartupEffective
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.CompactEuclideanEnergy

namespace OAI

/-! The compact Euclidean velocity is the input loader followed by the
machine-only periodic processor. Its full Navier--Stokes residual is affine
in viscosity and has the same fixed compact spatial support. -/

noncomputable section
namespace ForcedComputation.BalancedVelocity
open ShearFlows Set Filter
open scoped ContDiff Topology BigOperators

def velocity (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) : Velocity :=
  BalancedLoader.velocity (BalancedPlanar.inputCode I hI) + BalancedBody.activated I.1 hI.1

def support : Set Space := BalancedLoader.support ∪ BalancedBody.support

theorem support_compact : IsCompact support :=
  BalancedLoader.support_compact.union BalancedBody.support_compact

theorem smooth (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    ContDiff ℝ ∞ (velocity I hI) :=
  (BalancedLoader.velocity_smooth _).add (BalancedBody.activated_smooth _ _)

theorem supported (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) (t : ℝ) :
    tsupport (fun x => velocity I hI (t, x)) ⊆ support := by
  change tsupport ((fun x => BalancedLoader.velocity (BalancedPlanar.inputCode I hI) (t,x)) +
    (fun x => BalancedBody.activated I.1 hI.1 (t,x))) ⊆ support
  exact (tsupport_add _ _).trans (union_subset_union
    (BalancedLoader.velocity_support _ t) (BalancedBody.activated_support _ _ t))

theorem before (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {t : ℝ} (ht : t ≤ 1) (x : Space) :
    velocity I hI (t, x) = BalancedLoader.velocity (BalancedPlanar.inputCode I hI) (t, x) := by
  simp only [velocity, Pi.add_apply, BalancedBody.activated_before _ _ ht, add_zero]

theorem tail (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {t : ℝ} (ht : 1 ≤ t) (x : Space) :
    velocity I hI (t, x) = BalancedBody.velocity I.1 hI.1 (t, x) := by
  simp only [velocity, Pi.add_apply, BalancedBody.activated_tail _ _ ht,
    BalancedLoader.velocity_after _ (show (1 : ℝ) / 4 ≤ t by linarith), zero_add]

theorem zero_before (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {t : ℝ} (ht : t ≤ 1 / 8) (x : Space) : velocity I hI (t, x) = 0 := by
  rw [before I hI (by linarith), BalancedLoader.velocity_before _ ht]

theorem solenoidal (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    Solenoidal (velocity I hI) := by
  intro t x
  have hL : ContDiff ℝ ∞
      (fun z : Space => BalancedLoader.velocity (BalancedPlanar.inputCode I hI) (t,z)) :=
    (BalancedLoader.velocity_smooth (BalancedPlanar.inputCode I hI)).comp
    (contDiff_const.prodMk contDiff_id)
  have hB : ContDiff ℝ ∞ (fun z : Space => BalancedBody.activated I.1 hI.1 (t,z)) :=
    (BalancedBody.activated_smooth I.1 hI.1).comp
    (contDiff_const.prodMk contDiff_id)
  unfold divergence derivative
  change (∑ j, (fderiv ℝ
    ((fun z => BalancedLoader.velocity (BalancedPlanar.inputCode I hI) (t,z)) +
      (fun z => BalancedBody.activated I.1 hI.1 (t,z))) x) (basis j) j) = 0
  rw [fderiv_add (hL.differentiable (by simp) x) (hB.differentiable (by simp) x)]
  simp only [add_apply, Pi.add_apply,
    Finset.sum_add_distrib]
  change divergence (fun z => BalancedLoader.velocity (BalancedPlanar.inputCode I hI) (t,z)) x +
    divergence (fun z => BalancedBody.activation I.1 hI.1 t •
      BalancedBody.velocity I.1 hI.1 (t,z)) x = 0
  rw [BalancedLoader.velocity_divergence, divergence_smul,
    BalancedBody.velocity_divergence, mul_zero, add_zero]

theorem bounded (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    BoundedMixedDerivatives (velocity I hI) :=
  boundedMixed_of_compact_tail (smooth I hI) (BalancedBody.velocity_smooth _ _)
    support_compact (supported I hI)
    (fun t => (BalancedBody.velocity_support _ _ t).trans subset_union_right)
    (BalancedBody.velocity_periodic _ _)
    (fun _ ht x => zero_before I hI (by linarith) x)
    (fun _ ht x => tail I hI ht.le x)

private theorem residual_zero (ν : ℝ) : residual ν (fun _ : SpaceTime => (0 : Space)) = 0 := by
  have hd : derivative (fun _ : Space => (0 : Space)) = fun _ _ => 0 := by
    funext j x
    simp [derivative]
  have hl (x : Space) : laplacian (fun _ : Space => (0 : Space)) x = 0 := by
    simp only [laplacian, hd]
    apply Finset.sum_eq_zero
    intro j _
    rw [fderiv_const_apply]
    rfl
  funext y
  simp [residual, timeDerivative, advection, hl]

private theorem residual_supported {V : Velocity} {K : Set Space} (hK : IsClosed K)
    (hs : ∀ t, tsupport (fun x => V (t,x)) ⊆ K) (ν t : ℝ) :
    tsupport (fun x => residual ν V (t,x)) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  have ho : {y : SpaceTime | y.2 ∉ K} ∈ 𝓝 (t,x) :=
    (hK.isOpen_compl.preimage continuous_snd).mem_nhds hn
  have he : V =ᶠ[𝓝 (t,x)] fun _ => 0 := by
    filter_upwards [ho] with y hy
    exact image_eq_zero_of_notMem_tsupport (f := fun x : Space => V (y.1,x))
      (fun hm => hy (hs y.1 hm))
  apply hx
  change residual ν V (t,x) = 0
  rw [residual_congr_germ he ν, residual_zero]
  rfl

theorem residual_periodic {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hp : TimePeriodic V) (ν : ℝ) : TimePeriodic (residual ν V) := by
  intro t x
  rw [residual_eq_force_add, Pi.add_apply, force_time_periodic hV hp]
  congr 1
  simp only [convectiveField_eq_mixed hV]
  apply Finset.sum_congr rfl
  intro j _
  rw [hp t x, mixedDerivative_time_periodic hV hp [j.succ] t x]

theorem force_supported (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (ν t : ℝ) : tsupport (fun x => residual ν (velocity I hI) (t,x)) ⊆ support :=
  residual_supported support_compact.isClosed (supported I hI) ν t

theorem force_bounded (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) (ν : ℝ) :
    BoundedMixedDerivatives (residual ν (velocity I hI)) := by
  apply boundedMixed_of_compact_tail (residual_smooth (smooth I hI) ν)
    (residual_smooth (BalancedBody.velocity_smooth _ _) ν) support_compact
    (force_supported I hI ν)
    (residual_supported support_compact.isClosed
      (fun t => (BalancedBody.velocity_support _ _ t).trans subset_union_right) ν)
    (residual_periodic (BalancedBody.velocity_smooth _ _) (BalancedBody.velocity_periodic _ _) ν)
  · intro t ht x
    have he : velocity I hI =ᶠ[𝓝 (t,x)] fun _ => 0 := by
      filter_upwards [(continuous_fst.tendsto (t,x)).eventually (eventually_lt_nhds ht)] with y hy
      exact zero_before I hI (by linarith) y.2
    rw [residual_congr_germ he ν, residual_zero]
    rfl
  · intro t ht x
    apply residual_congr_germ
    filter_upwards [(continuous_fst.tendsto (t,x)).eventually (eventually_gt_nhds ht)] with y hy
    exact tail I hI hy.le y.2

def force₀ (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) : Velocity :=
  residual 0 (velocity I hI)

def force₁ (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) : Velocity :=
  fun y => -laplacian (fun x => velocity I hI (y.1,x)) y.2

theorem force_affine (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) (ν : ℝ) :
    residual ν (velocity I hI) = force₀ I hI + ν • force₁ I hI := by
  funext y
  simp only [residual, force₀, force₁, Pi.add_apply, Pi.smul_apply, zero_smul, sub_zero, smul_neg]
  rfl

end ForcedComputation.BalancedVelocity

end

end OAI
