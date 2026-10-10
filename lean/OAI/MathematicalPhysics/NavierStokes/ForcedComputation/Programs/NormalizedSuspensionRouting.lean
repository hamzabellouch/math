import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NormalizedDormantVelocity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.SparseSuspension

namespace OAI

/-! The finite geometric exclusion condition implies the exact one-period
material trajectory of the normalized stationary suspension. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar
open ShearFlows PlanarHamiltonian PlanarRouting PlanarTiming Set

/-- The pulse schedule, spatial clearance, ODE, endpoints and clock bounds
all come from the finite compiler. -/
theorem normalized_branch_suspension_in (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {x : Plane} (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (fun y =>
      SpatialExpression.suspensionField (normalizedHamiltonian I hI) y.2) Φ)
    {S : Set Plane} (hS : S ⊆ clockRectangle.carrier)
    (hp : ∀ k, normalizedAnchors I hI b x k ∈ S)
    (hcurve : ∀ k t, normalizedCurve I hI b x k t ∈ S) :
    Φ 1 (atHeight (normalizedAnchors I hI b x 0) 0) =
        atHeight (normalizedAnchors I hI b x 8) 1 ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        horizontal (Φ s (atHeight (normalizedAnchors I hI b x 0) 0)) ∈ S := by
  let n := (actions (freshMachine I.1) (freshInput_valid hI).1).length
  exact sparse_suspension (normalizedHamiltonian_valid I hI)
    (normalizedHamiltonian_periodic I hI) hΦ (N := n + 1) (by omega) (by omega)
    (branchIndices_strictMono _ _ b) (normalizedAnchors I hI b x) (normalizedCurve I hI b x)
    (cut n) (cut_zero n) (cut_last n) (fun i _ => cut_mono n (by omega))
    (normalizedCurve_start I hI b x) (normalizedCurve_finish I hI b x)
    (fun k => (normalizedCurve_smooth I hI b x k).continuous.continuousOn)
    (fun k s hs => normalizedCurve_ode I hI b hx k s ⟨hs.1, hs.2.le⟩)
    (normalized_sparseAnchor_zero I hI b hx) hS hp (fun k s _ => hcurve k s)

theorem normalized_branch_suspension (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {x : Plane} (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (fun y =>
      SpatialExpression.suspensionField (normalizedHamiltonian I hI) y.2) Φ) :
    Φ 1 (atHeight (normalizedAnchors I hI b x 0) 0) =
        atHeight (normalizedAnchors I hI b x 8) 1 ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        horizontal (Φ s (atHeight (normalizedAnchors I hI b x 0) 0)) ∈ clockRectangle.carrier := by
  exact normalized_branch_suspension_in I hI b hx hΦ (S := clockRectangle.carrier)
    Subset.rfl (normalizedAnchors_clock I hI b hx) (normalizedCurve_clock I hI b hx)

theorem normalized_branch_suspension_safe (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    (hn : recorderHalting (freshMachine I.1) b.target = false)
    {x : Plane} (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (fun y =>
      SpatialExpression.suspensionField (normalizedHamiltonian I hI) y.2) Φ) :
    Φ 1 (atHeight (normalizedAnchors I hI b x 0) 0) =
        atHeight (normalizedAnchors I hI b x 8) 1 ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        horizontal (Φ s (atHeight (normalizedAnchors I hI b x 0) 0)) ∈ {y : Plane | y ∈ clockRectangle.carrier ∧ 3 / 16 ≤ y 1} := by
  exact normalized_branch_suspension_in I hI b hx hΦ
    (S := {y : Plane | y ∈ clockRectangle.carrier ∧ 3 / 16 ≤ y 1})
    (fun _ h => h.1)
    (fun k => ⟨normalizedAnchors_clock I hI b hx k, normalizedAnchors_safe I hI b hn hx k⟩)
    (fun k t => ⟨normalizedCurve_clock I hI b hx k t, normalizedCurve_safe I hI b hn hx k t⟩)

end ForcedComputation.Recorder.Planar

end

end OAI
