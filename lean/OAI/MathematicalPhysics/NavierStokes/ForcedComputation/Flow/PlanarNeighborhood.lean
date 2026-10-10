import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarNeighborhoodMotion
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarConcatenation

namespace OAI

/-! The computed period map agrees with each branch's affine map on an
explicit positive open neighborhood of its entire closed source rectangle. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarRouting PlanarHamiltonian PlanarTiming Set

theorem branchNeighborhood_open (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : IsOpen (branchNeighborhood M hM b) := by
  have he : branchNeighborhood M hM b =
      ⋃ x ∈ (instruction M hM b).source.carrier, Metric.ball x (branchRadius M hM b : ℝ) := by
    ext y
    simp only [branchNeighborhood, mem_ofPred_eq, mem_iUnion, Metric.mem_ball, exists_prop]
  rw [he]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball

theorem normalized_branch_near_period (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {x y : Plane}
    (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    (hxy : dist y x < (branchRadius (freshMachine I.1) (freshInput_valid hI).1 b : ℝ))
    {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ψ) :
    Ψ 0 1 (normalizedAnchors I hI b y 0) = normalizedAnchors I hI b y 8 := by
  let n := (actions (freshMachine I.1) (freshInput_valid hI).1).length
  have h := sparse_planarTransition hΨ
    (planarSlice_lipschitz (normalizedHamiltonian_valid I hI) (normalizedHamiltonian_noTime I hI))
    (N := n + 1) (by omega) (by omega)
    (branchIndices_strictMono _ _ b) (normalizedAnchors I hI b y) (normalizedCurve I hI b y)
    (cut n) (cut_zero n) (cut_last n) (fun i _ => cut_mono n (by omega))
    (normalizedCurve_start I hI b y) (normalizedCurve_finish I hI b y)
    (fun k => (normalizedCurve_smooth I hI b y k).continuous.continuousOn)
    (fun k s hs => normalizedCurve_ode_near I hI b hx hxy k s ⟨hs.1, hs.2.le⟩)
    (normalized_sparseAnchor_zero_near I hI b hx hxy)
    (S := univ) (fun _ => mem_univ _) (fun _ _ _ => mem_univ _)
  exact h.1

theorem normalized_branch_neighborhood_period (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {y : Plane}
    (hy : y ∈ branchNeighborhood (freshMachine I.1) (freshInput_valid hI).1 b)
    {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ψ) :
    Ψ 0 1 (translatedPoint (initialShift (freshInput I) (freshInput_valid hI)) y) =
      translatedPoint (initialShift (freshInput I) (freshInput_valid hI))
        ((instruction (freshMachine I.1) (freshInput_valid hI).1 b).affine y) := by
  obtain ⟨x, hx, hxy⟩ := hy
  have h := normalized_branch_near_period I hI b hx hxy hΨ
  simpa only [normalizedAnchors, branchAnchors_first, branchAnchors_last] using h

end ForcedComputation.Recorder.Planar

end

end OAI
