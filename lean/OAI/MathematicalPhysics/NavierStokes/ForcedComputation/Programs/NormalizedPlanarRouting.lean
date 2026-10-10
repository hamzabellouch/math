import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NormalizedDormantVelocity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarConcatenation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarStepBranch

namespace OAI

/-! One complete period of the actual planar processor implements every
filled instruction rectangle and, consequently, each encoded machine step. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar
open ShearFlows PlanarHamiltonian PlanarRouting PlanarTiming Set

theorem normalized_branch_planar_in (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {x : Plane} (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ψ)
    {S : Set Plane} (hp : ∀ k, normalizedAnchors I hI b x k ∈ S)
    (hcurve : ∀ k t, normalizedCurve I hI b x k t ∈ S) :
    Ψ 0 1 (normalizedAnchors I hI b x 0) = normalizedAnchors I hI b x 8 ∧
      ∀ s ∈ Icc (0 : ℝ) 1, Ψ 0 s (normalizedAnchors I hI b x 0) ∈ S := by
  let n := (actions (freshMachine I.1) (freshInput_valid hI).1).length
  exact sparse_planarTransition hΨ
    (planarSlice_lipschitz (normalizedHamiltonian_valid I hI) (normalizedHamiltonian_noTime I hI))
    (N := n + 1) (by omega) (by omega)
    (branchIndices_strictMono _ _ b) (normalizedAnchors I hI b x) (normalizedCurve I hI b x)
    (cut n) (cut_zero n) (cut_last n) (fun i _ => cut_mono n (by omega))
    (normalizedCurve_start I hI b x) (normalizedCurve_finish I hI b x)
    (fun k => (normalizedCurve_smooth I hI b x k).continuous.continuousOn)
    (fun k s hs => normalizedCurve_ode I hI b hx k s ⟨hs.1, hs.2.le⟩)
    (normalized_sparseAnchor_zero I hI b hx) hp (fun k s _ => hcurve k s)

theorem normalized_branch_planar (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {x : Plane} (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ψ) :
    Ψ 0 1 (normalizedAnchors I hI b x 0) = normalizedAnchors I hI b x 8 ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        Ψ 0 s (normalizedAnchors I hI b x 0) ∈ clockRectangle.carrier :=
  normalized_branch_planar_in I hI b hx hΨ
    (normalizedAnchors_clock I hI b hx) (normalizedCurve_clock I hI b hx)

theorem normalized_branch_planar_safe (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    (hn : recorderHalting (freshMachine I.1) b.target = false)
    {x : Plane} (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ψ) :
    Ψ 0 1 (normalizedAnchors I hI b x 0) = normalizedAnchors I hI b x 8 ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        Ψ 0 s (normalizedAnchors I hI b x 0) ∈ {y : Plane | y ∈ clockRectangle.carrier ∧ 3 / 16 ≤ y 1} :=
  normalized_branch_planar_in I hI b hx hΨ
    (fun k => ⟨normalizedAnchors_clock I hI b hx k, normalizedAnchors_safe I hI b hn hx k⟩)
    (fun k s => ⟨normalizedCurve_clock I hI b hx k s, normalizedCurve_safe I hI b hn hx k s⟩)

theorem normalized_planar_step (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ψ)
    {C D : Configuration (State (freshMachine I.1)) (Alphabet (freshMachine I.1))}
    (hstep : Step (finiteMachine (freshMachine I.1) (freshInput_valid hI).1) C D) :
    Ψ 0 1 (shiftPoint (initialShift (freshInput I) (freshInput_valid hI))
      (point (freshMachine I.1) (freshInput_valid hI).1 C)) =
    shiftPoint (initialShift (freshInput I) (freshInput_valid hI))
      (point (freshMachine I.1) (freshInput_valid hI).1 D) := by
  obtain ⟨b, _, _, hx, he⟩ := step_branch hstep
  have h := (normalized_branch_planar I hI b hx hΨ).1
  simpa [normalizedAnchors, branchAnchors_first, branchAnchors_last, he, translatedPoint_eq_shiftPoint] using h

end ForcedComputation.Recorder.Planar

end

end OAI
