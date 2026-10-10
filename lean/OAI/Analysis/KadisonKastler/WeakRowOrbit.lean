import OAI.Analysis.KadisonKastler.WeakRowAction

namespace OAI

/-! Compact invariant weak closures of normalized finite-row orbits. -/

namespace KadisonKastler

noncomputable section

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance weakRowOrbitOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance weakRowOrbitStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

def boundedWeakRowOrbit {M : VonNeumannAlgebra H} {c : ℝ}
    (F : BoundedWeakAlgebraMap M c) : Set (BoundedWeakAlgebraMap M c) :=
  {G | G.map ∈ finiteRowOrbit F.map}

theorem boundedWeakRowOrbit_self {M : VonNeumannAlgebra H} {c : ℝ}
    (F : BoundedWeakAlgebraMap M c) : F ∈ boundedWeakRowOrbit F :=
  finiteRowOrbit_self F.map

theorem isCompact_closure_boundedWeakRowOrbit {M : VonNeumannAlgebra H} {c : ℝ}
    (hc : 0 ≤ c) (F : BoundedWeakAlgebraMap M c) :
    IsCompact (closure (boundedWeakRowOrbit F)) := by
  let : CompactSpace (BoundedWeakAlgebraMap M c) :=
    isCompact_univ_iff.mp (isCompact_boundedWeakAlgebraMap M hc)
  exact isClosed_closure.isCompact

theorem closure_boundedWeakRowOrbit_nonempty {M : VonNeumannAlgebra H} {c : ℝ}
    (F : BoundedWeakAlgebraMap M c) : (closure (boundedWeakRowOrbit F)).Nonempty :=
  ⟨F, subset_closure (boundedWeakRowOrbit_self F)⟩

theorem boundedWeakRowOrbit_invariant {M : VonNeumannAlgebra H} {c : ℝ}
    (hc : 0 ≤ c) (F : BoundedWeakAlgebraMap M c)
    {n : ℕ} (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1)
    {G : BoundedWeakAlgebraMap M c} (hG : G ∈ boundedWeakRowOrbit F) :
    boundedWeakRowAverage hc r hr G ∈ boundedWeakRowOrbit F :=
  finiteRowOrbit_invariant F.map hG r hr

theorem closure_boundedWeakRowOrbit_invariant {M : VonNeumannAlgebra H} {c : ℝ}
    (hc : 0 ≤ c) (F : BoundedWeakAlgebraMap M c)
    {n : ℕ} (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1)
    {G : BoundedWeakAlgebraMap M c} (hG : G ∈ closure (boundedWeakRowOrbit F)) :
    boundedWeakRowAverage hc r hr G ∈ closure (boundedWeakRowOrbit F) := by
  have hclosed : IsClosed {G : BoundedWeakAlgebraMap M c |
      boundedWeakRowAverage hc r hr G ∈ closure (boundedWeakRowOrbit F)} :=
    isClosed_closure.preimage (continuous_boundedWeakRowAverage hc r hr)
  have hsub : boundedWeakRowOrbit F ⊆ {G : BoundedWeakAlgebraMap M c |
      boundedWeakRowAverage hc r hr G ∈ closure (boundedWeakRowOrbit F)} := by
    intro G hg
    exact subset_closure (boundedWeakRowOrbit_invariant hc F r hr hg)
  exact closure_minimal hsub hclosed hG

end

end KadisonKastler

end OAI
