import OAI.Analysis.KadisonSimilarity.Representation.AmplifiedNormalRange
import OAI.Analysis.KadisonSimilarity.Representation.UnitaryNormalRange
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixTracialGNS
import OAI.Analysis.KadisonSimilarity.Tracial.TracialBoundedBalls

namespace OAI

/-! The native matrix GNS representation has normal range whenever the
original native GNS representation does. -/

noncomputable section
namespace KadisonSimilarity
open scoped CStarAlgebra ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (M : VonNeumannAlgebra τ.GNS)
  (hrange : τ.gnsStarAlgHom.range = M.toStarSubalgebra)
  (n : ℕ) [NeZero n]

include hrange in
theorem matrix_gns_normal_range :
    (normalizedMatrixTrace τ n).gnsStarAlgHom.range =
      (representationVonNeumannAlgebra (normalizedMatrixTrace τ n).gnsStarAlgHom).toStarSubalgebra := by
  let σ := amplifiedScalarRepresentation τ.gnsStarAlgHom n
  let N := (matrixVonNeumann M.commutant n).commutant
  have hσ : σ.range = N.toStarSubalgebra :=
    amplifiedScalarRepresentation_normal_range τ.gnsStarAlgHom M hrange n
  let ρ := representedMatrixHom σ n
  have hρ : ρ.range = (matrixVonNeumann N n).toStarSubalgebra :=
    representedMatrixHom_range σ N hσ n
  apply normal_range_of_unitary_intertwining
    (normalizedMatrixTrace τ n).gnsStarAlgHom ρ (matrixGNSUnitary τ n) ?_ _ hρ
  intro X
  ext ξ
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, matrixGNSUnitary_left,
    LinearIsometryEquiv.apply_symm_apply]
  rfl

include hrange in
theorem matrix_trace_balls_closed (h1 : τ 1 = 1)
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hf : ∀ a, τ (star a * a) = 0 → a = 0) (C : ℝ) :
    IsClosed (gnsTracialVector (normalizedMatrixTrace τ n) ''
      Metric.closedBall (0 : CStarMatrix (Fin n) (Fin n) A) C) := by
  let τn := normalizedMatrixTrace τ n
  let htrn := normalizedMatrixTrace_tracial τ htr (n := n)
  let G := gnsTracialGeometry τn htrn
  exact G.trace_balls_closed_of_normal_range (normalizedMatrixTrace_one τ h1)
    (gnsTracialVector_injective τn (normalizedMatrixTrace_faithful τ hf)) _
    (matrix_gns_normal_range τ M hrange n) C

end KadisonSimilarity

end

end OAI
