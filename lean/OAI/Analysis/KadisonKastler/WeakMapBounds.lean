import OAI.Analysis.KadisonKastler.WeakRowAction

namespace OAI

/-! Complete norm sublevel sets are closed in the pointwise weak topology. -/

namespace KadisonKastler

noncomputable section

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance weakMapBoundsOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance weakMapBoundsStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

def boundedWeakMapInclusion {M : VonNeumannAlgebra H} {c d : ℝ} (hdc : d ≤ c)
    (F : BoundedWeakAlgebraMap M d) : BoundedWeakAlgebraMap M c :=
  ⟨F.map, F.bound.mono hdc⟩

theorem continuous_boundedWeakMapInclusion {M : VonNeumannAlgebra H} {c d : ℝ} (hdc : d ≤ c) :
    Continuous (boundedWeakMapInclusion (M := M) hdc) := by
  apply continuous_induced_rng.mpr
  change Continuous (boundedWeakAlgebraCoefficients (M := M) (c := d))
  exact continuous_induced_dom

theorem isClosed_completelyBoundedBy {M : VonNeumannAlgebra H} {c d : ℝ} (hd : 0 ≤ d) :
    IsClosed {F : BoundedWeakAlgebraMap M c | CompletelyBoundedBy F.map d} := by
  classical
  by_cases hdc : d ≤ c
  · have hrange : Set.range (boundedWeakMapInclusion (M := M) hdc) =
        {F : BoundedWeakAlgebraMap M c | CompletelyBoundedBy F.map d} := by
      ext F
      constructor
      · rintro ⟨G, rfl⟩
        exact G.bound
      · intro hF
        refine ⟨⟨F.map, hF⟩, ?_⟩
        cases F
        rfl
    have hcompact := (isCompact_boundedWeakAlgebraMap M hd).image
      (continuous_boundedWeakMapInclusion (M := M) hdc)
    rw [Set.image_univ, hrange] at hcompact
    exact hcompact.isClosed
  · have he : {F : BoundedWeakAlgebraMap M c | CompletelyBoundedBy F.map d} = Set.univ := by
      ext F
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact F.bound.mono (le_of_not_ge hdc)
    rw [he]
    exact isClosed_univ

end

end KadisonKastler

end OAI
