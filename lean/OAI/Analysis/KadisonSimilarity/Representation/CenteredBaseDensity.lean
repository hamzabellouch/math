import OAI.Analysis.KadisonSimilarity.FreeProduct.BaseSymmetry

namespace OAI

/-! Trace-zero algebra elements are dense in the actual centered base space.
This extends elementary reduced-word identities to completed tensor letters. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)]

/-- The trace-zero algebra elements, with their actual centered Hilbert vectors. -/
def centeredBaseAlgebraVector (a : {a : A // G.trace (a : P) = 0}) :
    centeredSubspace (G.baseVector A 1) := G.baseSymmetryLetter A a.val a.property

theorem centeredBaseAlgebraVector_dense (hτ : G.trace 1 = 1) :
    DenseRange (G.centeredBaseAlgebraVector A) := by
  have hd := denseRange_tracialCenter (G.baseVector A) (G.baseVector_dense A)
  apply hd.mono
  rintro _ ⟨a, rfl⟩
  let a₀ : A := a - G.trace (a : P) • 1
  have ha₀ : G.trace (a₀ : P) = 0 := by
    change (G.baseGeometry A).trace (a - (G.baseGeometry A).trace a • 1) = 0
    exact trace_sub_trace _ (G.baseGeometry_trace_one A hτ) a
  refine ⟨⟨a₀, ha₀⟩, ?_⟩
  apply Subtype.ext
  change G.baseVector A a₀ = (tracialCenter (G.baseVector A) a : G.baseSpace A)
  rw [coe_tracialCenter (G.baseGeometry A).trace (G.baseVector A)
    (G.baseVector_inner A) (G.baseGeometry_trace_one A hτ)]
  change G.baseVector A (a - G.trace (a : P) • 1) = _
  rw [map_sub, map_smul]
  rfl

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
