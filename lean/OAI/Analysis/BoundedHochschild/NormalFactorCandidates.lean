import OAI.Analysis.BoundedHochschild.RepresentedAveragingOrbit
import OAI.Analysis.BoundedHochschild.NormalGNSWeakTopology

namespace OAI

/-! The compact factorization construction for the given W*-algebra predual. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem normalGNS_representation_ball_closed (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (C : ℝ) :
    IsClosed (representationWeakBall (normalGNSRepresentation e) C) :=
  normalGNSWeak_ball_isClosed e C

theorem normalGNS_factorization [Nontrivial M] (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : M →L[ℂ] M) {C : ℝ} (hC : 0 < C) (hT : CompletelyBoundedEstimate T C) :
    Nonempty (OperatorFactorization
      ((normalGNSRepresentation e).toLinearMap.comp T.toLinearMap) C) := by
  let := normalGNS_nontrivial e
  exact represented_factorization (normalGNSRepresentation e) T hC hT

end BoundedHochschild.KadisonRingrose

end

end OAI
