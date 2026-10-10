import OAI.Analysis.Hyperinvariant.Witness
import OAI.Analysis.Hyperinvariant.HilbertClassification
import OAI.Analysis.Hyperinvariant.Transport
import OAI.Analysis.Hyperinvariant.CommutantTopology

namespace OAI

namespace Hyperinvariant
universe u
variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- Every infinite-dimensional separable complex Hilbert space admits a nonzero
norm-quasinilpotent operator with a proper strongly closed transitive commutant. -/
theorem main_theorem (hInf : ¬FiniteDimensional ℂ H) : FullClaim (H := H) := by
  let : Nontrivial H := not_subsingleton_iff_nontrivial.mp (by
    intro hs
    let : Subsingleton H := hs
    exact hInf inferInstance)
  obtain ⟨e⟩ := nonempty_linearIsometryEquiv
    (H := FiniteFactor.SourceHilbert FiniteFactor.SourceCoordinate)
    (K := H) source_infiniteDimensional hInf
  exact fullClaim_of_mainClaim (mainClaim_transport e source_mainClaim)

end Hyperinvariant

end OAI
