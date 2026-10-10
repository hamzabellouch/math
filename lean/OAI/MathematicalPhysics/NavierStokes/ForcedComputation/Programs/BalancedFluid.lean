import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedPath
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedEuclidean

namespace OAI

/-! The compact balanced application: a machine-only repeated field, a
finite initial loader, and the fixed open-cube material observation. -/

noncomputable section
namespace ForcedComputation.Balanced
open ShearFlows Set Filter Recorder.Planar RapidForcing.CompactEmbedding
open scoped ContDiff Topology

def velocity (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) : Velocity :=
  BalancedVelocity.velocity I hI

def force (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) (ν : ℝ) : Velocity :=
  residual ν (velocity I hI)

def initialLabel : AlternatingNS.Space := piCoordinates.symm ![4,0,0]

def observer : Set AlternatingNS.Space := {x | ∀ j : Fin 3, -1 < x j ∧ x j < 2}

theorem force_tail (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (ν : ℝ) {t : ℝ} (ht : 1 ≤ t) (x : Space) :
    force I hI ν (t,x) = residual ν (BalancedBody.velocity I.1 hI.1) (t,x) := by
  have he : EqOn (fun s => force I hI ν (s,x))
      (fun s => residual ν (BalancedBody.velocity I.1 hI.1) (s,x)) (Ioi 1) := by
    intro s hs
    apply residual_congr_germ
    filter_upwards [(continuous_fst.tendsto (s,x)).eventually
      (eventually_gt_nhds hs)] with y hy
    exact BalancedVelocity.tail I hI hy.le y.2
  have h₁ : Continuous (fun s => force I hI ν (s,x)) :=
    (residual_smooth (BalancedVelocity.smooth I hI) ν).continuous.comp
      (continuous_id.prodMk continuous_const)
  have h₂ : Continuous (fun s => residual ν (BalancedBody.velocity I.1 hI.1) (s,x)) :=
    (residual_smooth (BalancedBody.velocity_smooth I.1 hI.1) ν).continuous.comp
      (continuous_id.prodMk continuous_const)
  exact he.closure h₁ h₂ (by
    rw [closure_Ioi]
    change 1 ≤ t
    exact ht)

theorem force_tail_periodic (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (ν : ℝ) {t : ℝ} (ht : 1 ≤ t) (x : Space) :
    force I hI ν (t+1,x) = force I hI ν (t,x) := by
  rw [force_tail I hI ν (by linarith), force_tail I hI ν ht]
  exact BalancedVelocity.residual_periodic
    (BalancedBody.velocity_smooth I.1 hI.1)
    (BalancedBody.velocity_periodic I.1 hI.1) ν t x

/-- Every clause refers to the named prescribed force and its actual
Euclidean Navier--Stokes solution. -/
def FluidProperties (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (ν : ℝ) : Prop :=
  let V := velocity I hI
  let f := force I hI ν
  let U := CompactEuclidean.velocity V
  let F := CompactEuclidean.velocity f
  ContDiff ℝ ∞ V ∧ ContDiff ℝ ∞ f ∧
  BoundedMixedDerivatives V ∧ BoundedMixedDerivatives f ∧
  (∀ t, tsupport (fun x => V (t,x)) ⊆ BalancedVelocity.support ∧
    tsupport (fun x => f (t,x)) ⊆ BalancedVelocity.support) ∧
  (∀ t, 1 ≤ t → ∀ x, V (t,x) = BalancedBody.velocity I.1 hI.1 (t,x) ∧
    V (t+1,x) = V (t,x) ∧
    f (t,x) = residual ν (BalancedBody.velocity I.1 hI.1) (t,x) ∧
    f (t+1,x) = f (t,x)) ∧
  AlternatingNS.NavierStokes ν F U (fun _ _ => 0) ∧
  AlternatingNS.EnergyClass U (fun _ _ => 0) ∧
  (∀ v p, CompactEuclidean.IsEnergySolutionModuloConstants ν F v p →
    ∃ c : ℝ → ℝ, ∀ t, 0 ≤ t → ∀ x, v t x = U t x ∧ p t x = c t) ∧
  ∃ X : AlternatingNS.Space → ℝ → AlternatingNS.Space,
    (∀ a, AlternatingNS.IsTrajectory U a (X a)) ∧
    (∀ a γ, AlternatingNS.IsTrajectory U a γ → ∀ t, 0 ≤ t → γ t = X a t) ∧
    ((∃ t, 0 ≤ t ∧ X initialLabel t ∈ observer) ↔ Alternating.Halts I)

theorem fluid_properties (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {ν : ℝ} (hν : 0 < ν) : FluidProperties I hI ν := by
  have hs := BalancedVelocity.smooth I hI
  have hsupport (t : ℝ) : Function.support (fun x => velocity I hI (t,x)) ⊆
      BalancedVelocity.support :=
    (subset_tsupport _).trans (BalancedVelocity.supported I hI t)
  obtain ⟨hsol,hE,huniq⟩ := CompactEuclidean.compact_prescribed_solution hν hs
    BalancedVelocity.support_compact hsupport
    (fun x => BalancedVelocity.zero_before I hI (by norm_num) x)
    (BalancedVelocity.solenoidal I hI)
  obtain ⟨X,hX,hXuniq⟩ := CompactEuclidean.velocity_global_material_flow hs
    BalancedVelocity.support_compact hsupport
  refine ⟨hs, residual_smooth hs ν, BalancedVelocity.bounded I hI,
    BalancedVelocity.force_bounded I hI ν,
    fun t => ⟨BalancedVelocity.supported I hI t, BalancedVelocity.force_supported I hI ν t⟩,
    fun t ht x => ⟨BalancedVelocity.tail I hI ht x,
      by
        change BalancedVelocity.velocity I hI (t+1,x) = BalancedVelocity.velocity I hI (t,x)
        rw [BalancedVelocity.tail I hI (by linarith), BalancedVelocity.tail I hI ht,
          BalancedBody.velocity_periodic],
      force_tail I hI ν ht x, force_tail_periodic I hI ν ht x⟩,
    hsol,hE,huniq,X,hX,hXuniq,?_⟩
  obtain ⟨Ψ,hΨ⟩ := compactVelocity_transitions (BalancedPlanar.referenceInput I.1)
    (BalancedPlanar.referenceValid hI.1)
  obtain ⟨Ω,hΩ⟩ := exists_planarTransition
    (normalizedHamiltonian_valid (BalancedPlanar.referenceInput I.1)
      (BalancedPlanar.referenceValid hI.1))
    (normalizedHamiltonian_noTime (BalancedPlanar.referenceInput I.1)
      (BalancedPlanar.referenceValid hI.1))
  let γ : ℝ → AlternatingNS.Space := fun t => piCoordinates.symm (BalancedPath.path I hI Ψ t)
  have hγ : AlternatingNS.IsTrajectory (CompactEuclidean.velocity (velocity I hI))
      initialLabel γ := by
    refine ⟨congrArg piCoordinates.symm (BalancedPath.path_initial I hI Ψ),?_⟩
    intro t _
    let : AddCommGroup AlternatingNS.Space := WithLp.instAddCommGroup 2 (Fin 3 → ℝ)
    let : Module ℝ AlternatingNS.Space := WithLp.instModule 2 ℝ (Fin 3 → ℝ)
    let : TopologicalSpace AlternatingNS.Space := PiLp.topologicalSpace 2 (fun _ : Fin 3 => ℝ)
    let lift : Space →L[ℝ] AlternatingNS.Space :=
      { toFun := fun x => WithLp.toLp 2 x
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        cont := PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ) }
    have hd := lift.hasFDerivAt.comp_hasDerivAt t (BalancedPath.path_deriv I hI hΨ t)
    convert hd.hasDerivWithinAt (s := Ici 0) using 1 <;>
      simp only [γ, lift, Function.comp_def, CompactEuclidean.velocity, velocity,
        piCoordinates, ContinuousLinearEquiv.apply_symm_apply] <;> rfl
  have he (t : ℝ) (ht : 0 ≤ t) : γ t = X initialLabel t := hXuniq _ _ hγ t ht
  have hob := BalancedPath.path_observation I hI hΨ hΩ
  constructor
  · rintro ⟨t,ht,hobs⟩
    apply hob.mp
    refine ⟨t,ht,?_⟩
    intro j
    have hj := hobs j
    rw [← he t ht] at hj
    change -1 < piCoordinates.symm (BalancedPath.path I hI Ψ t) j ∧
      piCoordinates.symm (BalancedPath.path I hI Ψ t) j < 2 at hj
    exact hj
  · intro hh
    obtain ⟨t,ht,hobs⟩ := hob.mpr hh
    refine ⟨t,ht,?_⟩
    intro j
    rw [← he t ht]
    exact hobs j

end ForcedComputation.Balanced

end

end OAI
