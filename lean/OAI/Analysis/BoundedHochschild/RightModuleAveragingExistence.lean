import OAI.Analysis.BoundedHochschild.ProjectionDefectRigidity
import OAI.Analysis.BoundedHochschild.ProjectionModuleMaps
import OAI.Analysis.BoundedHochschild.LiftedOrbitRealization
import OAI.Analysis.BoundedHochschild.RightModuleFixedPoints

namespace OAI

/-! A completely bounded map on the properly infinite algebra has a right
module map in its original weak-star closed averaging orbit. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_right_module_average [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    (T : M →L[ℂ] M) {C : ℝ} (hC : 0 < C) (hT : CompletelyBoundedEstimate T C) :
    ∃ S : M →L[ℂ] M, ‖S‖ ≤ C ∧ weakOperatorImage e S ∈ weakRightAverageOrbit e T ∧
      ∀ a b : M, S (a * b) = S a * b := by
  obtain ⟨D⟩ := normalGNS_factorization e T hC hT
  let π := D.representation
  let L := D.leftMap
  let W := D.rightMap
  have hfac : ∀ a, normalGNSRepresentation e (T a) = L.adjoint.comp ((π a).comp W) :=
    D.factorization
  obtain ⟨F, hFsub, hFne, hFc, hFv, hFi, hFm⟩ := exists_minimal_represented_averages
    π (normalGNSRepresentation e) (ContinuousLinearMapWOT.ofCLM W)
  obtain ⟨V, hV⟩ := hFne
  obtain ⟨S, hSC, hSorb, hSfac⟩ := lifted_orbit_realization e hno T hT π L W hfac (hFsub hV)
  refine ⟨S, hSC, hSorb, ?_⟩
  apply right_module_of_projection_defects e S
  intro a p hp
  exact projection_defect_eq_zero e π L V.toCLM S hSfac
    (fun f hf => minimal_family_projection_norm e π F hFc hFv hFi hFm V hV hf) a hp

end BoundedHochschild.KadisonRingrose

end

end OAI
