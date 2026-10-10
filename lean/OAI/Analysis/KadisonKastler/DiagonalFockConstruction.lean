import OAI.Analysis.KadisonKastler.FreeDiagonalCompression

namespace OAI

/-! # The required faithful finite-diagonal Fock representation

This proves the precise structural representation input used in the
projection-word estimates, from reduced centered words in the faithful
tracial GNS Hilbert space.
-/

namespace KadisonKastler

noncomputable section

universe u

theorem publishedDiagonalFockRepresentation : PublishedDiagonalFockRepresentation.{u} := by
  intro B _ r d _ τ e hp ho hs _ hf
  let A := generatedDiagonal e
  let : PartialOrder A := CStarAlgebra.spectralOrder _
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing _
  let σ := generatedDiagonalTrace τ e
  let e' := generatedDiagonalProjection e
  let F := tracialDiagonalFockModel σ e'
    (generatedDiagonalProjection_isProjection e hp)
    (generatedDiagonalProjection_orthogonal e ho)
    (generatedDiagonalProjection_sum e hs)
    (generatedDiagonal_scalarFree τ e hf)
    (generatedDiagonal_generatedProjection_eq_top e)
  refine ⟨TraceStateHilbert σ, inferInstance, inferInstance, inferInstance,
    F, traceStateRepresentation σ, traceStateRepresentation_injective σ, ?_⟩
  intro i a
  rfl

end

end KadisonKastler

end OAI
