import OAI.Analysis.KadisonKastler.MinimalRowDynamics
import OAI.Analysis.KadisonKastler.WeakMapBounds

namespace OAI

/-! Complete norm bounds agree throughout a minimal row family. -/

namespace KadisonKastler

noncomputable section

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance minimalRowBoundsOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance minimalRowBoundsStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem minimal_row_family_complete_bound {M : VonNeumannAlgebra H} {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (K : Set (BoundedWeakAlgebraMap M c)) (hclosed : IsClosed K)
    (hinv : RowInvariant hc K)
    (hmin : ∀ L : Set (BoundedWeakAlgebraMap M c), L ⊆ K → L.Nonempty → IsClosed L →
      RowInvariant hc L → L = K)
    {F G : BoundedWeakAlgebraMap M c} (hF : F ∈ K) (hG : G ∈ K)
    (hbound : CompletelyBoundedBy F.map d) : CompletelyBoundedBy G.map d := by
  have hs : boundedWeakRowOrbit F ⊆
      {T : BoundedWeakAlgebraMap M c | CompletelyBoundedBy T.map d} := by
    intro T hT
    obtain ⟨n, r, hr, he⟩ := hT
    change CompletelyBoundedBy T.map d
    rw [he]
    exact hbound.finiteRightAverage hd r hr
  have hcl := closure_minimal hs (isClosed_completelyBoundedBy (M := M) hd)
  rw [minimal_row_family_orbit_dense hc K hclosed hinv hmin hF] at hcl
  exact hcl hG

end

end KadisonKastler

end OAI
