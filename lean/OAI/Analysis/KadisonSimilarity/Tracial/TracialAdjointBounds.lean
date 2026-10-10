import OAI.Analysis.KadisonSimilarity.Tracial.TracialBaseSpace
import OAI.Analysis.KadisonSimilarity.Representation.AdjointCommutators

namespace OAI

/-! The same corner hypotheses hold for the adjoint operator, so the
propagation argument supplies both errors in the final compression. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

theorem adjoint_commutes_with_base (D : StarSubalgebra ℂ P) (Y : H →L[ℂ] H)
    (hY : ∀ x : D, Y.comp (G.left (x : P)) = (G.left (x : P)).comp Y) (x : D) :
    Y.adjoint.comp (G.left (x : P)) = (G.left (x : P)).comp Y.adjoint := by
  have hx : (G.left (star (x : P))).adjoint = G.left (x : P) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_star]
  have h := congrArg (fun T : H →L[ℂ] H => T.adjoint) (hY (star x))
  simpa only [ContinuousLinearMap.adjoint_comp, StarMemClass.coe_star, hx] using h.symm

theorem adjoint_corner_commutator_bound (e : P) (he : IsStarProjection e)
    (Y : H →L[ℂ] H) {ε : ℝ}
    (hY : ∀ x : CStarCorner e he, ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
    (x : CStarCorner e he) :
    ‖commutator Y.adjoint (G.left (x : P))‖ ≤ ε * ‖x‖ := by
  have hx : star (G.left (x : P)) = G.left (star (x : P)) := (map_star G.left _).symm
  change ‖commutator (star Y) (G.left (x : P))‖ ≤ _
  rw [norm_commutator_adjoint_left, hx]
  have h := hY (star x)
  simpa only [StarMemClass.coe_star, norm_star] using h

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
