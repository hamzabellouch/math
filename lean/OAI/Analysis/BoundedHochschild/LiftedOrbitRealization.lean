import OAI.Analysis.BoundedHochschild.AveragingOrbitFactorization

namespace OAI

/-! The lifted operator orbit maps back into the original weak-star averaging
orbit, including at its boundary. -/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem lifted_orbit_realization (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) (T : M →L[ℂ] M) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C)
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L W : NormalGNS e →L[ℂ] K)
    (hfac : ∀ a, normalGNSRepresentation e (T a) = L.adjoint.comp ((π a).comp W))
    {V : NormalGNS e →WOT[ℂ] K}
    (hV : V ∈ closedRepresentedAveragingOrbit π (normalGNSRepresentation e)
      (ContinuousLinearMapWOT.ofCLM W)) :
    ∃ S : M →L[ℂ] M, ‖S‖ ≤ C ∧ weakOperatorImage e S ∈ weakRightAverageOrbit e T ∧
      ∀ a, normalGNSRepresentation e (S a) = L.adjoint.comp ((π a).comp V.toCLM) := by
  let B := weakNormalOperatorFamily e '' weakRightAverageOrbit e T
  have hBc : IsClosed B := ((weakRightAverageOrbit_isCompact e hno T hT).image
    (weakNormalOperatorFamily_continuous e)).isClosed
  have hpre : IsClosed (weakFactorFamily π L ⁻¹' B) :=
    hBc.preimage (weakFactorFamily_continuous π L)
  have hsub : representedAveragingOrbit π (normalGNSRepresentation e)
      (ContinuousLinearMapWOT.ofCLM W) ⊆ weakFactorFamily π L ⁻¹' B := by
    rintro V ⟨n, m, hm, rfl⟩
    refine ⟨weakOperatorImage e (finiteRightAverage m T),
      subset_closure ⟨finiteRightAverage m T, finiteRightAverage_mem_orbit m hm T, rfl⟩, ?_⟩
    funext a
    rw [weakNormalOperatorFamily_image]
    exact congrArg ContinuousLinearMapWOT.ofCLM
      (representedRightAverage_factorization π (normalGNSRepresentation e) T L W hfac m a)
  obtain ⟨F, hF, he⟩ := closure_minimal hsub hpre hV
  obtain ⟨S, hSC, hSF⟩ := weakOperatorBall_realize e hT.1
    (weakRightAverageOrbit_subset_ball e hno T hT hF)
  refine ⟨S, hSC, hSF ▸ hF, fun a => ?_⟩
  have hh := congrFun he a
  rw [← hSF, weakNormalOperatorFamily_image] at hh
  exact congrArg ContinuousLinearMapWOT.toCLM hh

end BoundedHochschild.KadisonRingrose

end

end OAI
